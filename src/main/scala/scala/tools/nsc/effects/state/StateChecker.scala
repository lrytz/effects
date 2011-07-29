package scala.tools.nsc.effects
package state

import scala.tools.nsc._
import scala.collection.{immutable => i}
import pc._

class StateChecker(val global: Global) extends EffectChecker[StateLattice] with ConvertAnnots with PCTracking[StateLattice] {
  import global._
  import analyzer.{Typer, Context}

  val runsAfter = List("stateInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "stateChecker"


  val lattice = new StateLattice {
    val global: StateChecker.this.global.type = StateChecker.this.global
  }
  import lattice.{Locality, AnyLoc, LocSet,
                  Location, SymLoc, Fresh, ThisLoc,
                  Store, StoreAny, StoreLoc,
                  Assignment, AssignAny, AssignLoc,
                  join, joinStore, joinAssignment, joinLocality,
                  sequence,
                  mkElem}

  
  import pcCommons._
  import pcLattice.{PC, PCInfo, AnyPC}
  
  
  override def newEffectTraverser(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(rhs, EnvMap(), rhsTyper, sym, unit)


  trait Env {
    
    /**
     * Apply an effect to this environemnt.
     * 
     * The `@assign` effects are applied first, which is a conservative result.
     * Example: take a nested function that does both, assigning outer variables
     * and storing values.
     * 
     *   def foo(a: A, b: B, c: C) {
     *     var x = b
     *     def inner() { a.store(x); x = c }
     *     inner()
     *     x
     *   }
     *
     * The effect of `inner` is `@store(a, x) @assign(x, c)`. When applying this
     * effect to the environemnt `x -> {b}`, the assignment effect is treated first.
     * This gives
     *
     *   env(x -> {b})            |  assign(x, c)
     *   env(x -> {b, c})         |  store(a, x)
     *   env(x -> {b, c},
     *       a -> {a, b, c}
     *       b -> {a, b, c}
     *       c -> {a, b, c})
     * 
     * The resulting environemnt is over-approximated, if we knew the store effect
     * happens first, the result would be more precise.
     * 
     * This is correct because an assign can influence a store, but not the other way
     * around; if a store happens before an assign, the assign will already have the
     * merged locality. Example
     * 
     *   def inner() { c.store(a); x = c }
     * 
     * has effect `@store(c, a) @assign(x, (c, a))`.
     * 
     * @TODO: what if there are multiple @assign and / or multiple @store? compute fixpoint?
     */
    def applyEffect(eff: Elem): Env = this match {
      case AnyEnv =>
        AnyEnv

      case EnvMap(m, localsTo) =>
        val assignEnv = eff._2 match {
          case AssignAny(to) =>
            val (localVarsMap, othersMap) = m.partition(e => e._1.isLocalVar)
            val assignedLocality = (to :: localVarsMap.map(_._2).toList).reduceRight(joinLocality)
            val resLocality = localsTo.map(l => joinLocality(l, assignedLocality)).orElse(Some(assignedLocality))
            EnvMap(othersMap, resLocality)
            
          case assgn @ AssignLoc(strong, weak) =>
            if (localsTo.isEmpty) {
              EnvMap(m, localsTo.map(l => joinLocality(l, assgn.assignedLocality)))
            } else {
              val strongMap = (m /: strong) {
                case (m, (to, from)) =>
                  m.updated(to, from)
              }
              val resMap = (strongMap /: weak) {
                case (m, (to, from)) =>
                  val res = m.get(to).map(joinLocality(_, from)).getOrElse(from)
                  m.updated(to, res)
              }
              EnvMap(resMap, localsTo)
            }
        }

        val storeEnv = eff._1 match {
          case StoreAny =>
            AnyEnv

          case StoreLoc(effs) =>
            // @TODO: assumes that the locations in `effs` are parameters / outer variables.
            // if there are local variables, their locality can change and the environment
            // would be not well formed.
            val resMap = (assignEnv.m /: effs) {
              case (m, (in, from)) =>
                from.s.toList match {
                  case Nil | List(Fresh) => m
                  case _ =>
                    // all involved locations
                    val modifiedLocs = from.union(LocSet(in))
                    (m /: modifiedLocs.s) {
                      case (m, loc) => m.updated(loc, modifiedLocs)
                    }
                }
            }
            EnvMap(resMap, assignEnv.localsTo)
        }

        storeEnv
    }

  }
  case class EnvMap(m: Map[Location, Locality] = Map(), localsTo: Option[Locality] = None) extends Env
  case object AnyEnv extends Env

  
  def subtreeEffect(tree: Tree, env: Env, localTyper: Typer, sym: Symbol, unit: CompilationUnit): Elem = {
    new StateTraverser(tree, env, localTyper, sym, unit).compute()
  }

  class StateTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends EffectTraverser(rhs, rhsTyper, sym, unit) {
    def subtreeEffect(tree: Tree, newEnv: Env) = StateChecker.this.subtreeEffect(tree, newEnv, rhsTyper, sym, unit)

    override def traverse(tree: Tree) {
      tree match {
        // Apply, TypeApply: handled ok in superclass (EffectTraverser, call to handleApplication)

        case Select(_, _) =>
          if (tree.symbol.isMethod) {
            // applications to parameterless methods are `Select` trees, e.g. getters
            handleApplication(tree)
          } else {
            // TODO: handle selection of other things. (like what? objects, for instance)
          }

        case Ident(name) =>
          val sym = tree.symbol
          if (sym.isMethod) {
            handleApplication(tree)
          } else {
            // an Ident tree can refer to parameters, local values or packages in the `root` package.
            if (sym.owner.isRootPackage) mkElem(AnyLoc)
            else mkElem(LocSet(SymLoc(tree.symbol))) // @TODO: is this OK for local objects? maybe instead of putting SymLoc for everything else, make specific tests for params, locals to create a SymLoc, and AnyLoc otherwise.
          }


        case Assign(lhs, rhs) =>
          val lhsEffect = subtreeEffect(lhs, env)
          val lhsEnv = env.applyEffect(lhsEffect)
          
          val rhsEffect = subtreeEffect(rhs, lhsEnv)
          // val rhsEnv = lhsEnv.applyEffect(rhsEffect) // not needed

          val parts = sequence(lhsEffect, rhsEffect)
          
          val lhsLoc = lhsEffect._3 match {
            case LocSet(s) =>
              assert(s.size == 1)
              s.toList(0)
          }
          
          val assignEff = mkElem(AssignLoc(lhsLoc, rhsEffect._3, true)) // @TOOD: don't do this if `lhsLoc` and `rhsEffect._3` are fresh
          val resEff = sequence(parts, assignEff)
          add((resEff._1, resEff._2, LocSet())) // no value is returned, so there's no locality

        case Block(stats, expr) =>
          val (statsEff, statsEnv) = (stats :\ (lattice.bottom, env)) {
            case (stat, (eff, env)) =>
              val e = subtreeEffect(stat, env)
              (sequence(eff, e), env.applyEffect(e))
          }
          
          val exprEff = subtreeEffect(expr, statsEnv)
          add(sequence(statsEff, exprEff))

        case If(cond, thenExpr, elseExpr) =>
          val condEff = subtreeEffect(cond, env)
          val condEnv = env.applyEffect(condEff)
          
          val thenEff = subtreeEffect(thenExpr, condEnv)
          val elseEff = subtreeEffect(elseExpr, condEnv)
          
          val resEff = sequence(condEff, join(thenEff, elseEff))
          add(resEff)
          
        case New(tpt) =>
          // no side effects - the constructor call is represented as a separate Apply tree
          add((StoreLoc(), AssignLoc(), LocSet(Fresh)))
        
        case Super(qual, mix) =>
          add(StoreLoc(), AssignLoc(), LocSet(ThisLoc(tree.symbol)))

        case This(qual) =>
          add(StoreLoc(), AssignLoc(), LocSet(ThisLoc(tree.symbol)))

        case Literal(c) =>
          add(StoreLoc(), AssignLoc(), LocSet(Fresh))
          
        // @TODO
        case Try(block, catches, finalizer) =>
          ()
        
        // @TODO
        case Return(expr) =>
          ()

        // @TODO: CaseDef, Match etc
          
        case _ =>
          super.traverse(tree)
      }
        
    }

    override def handleApplication(tree: Tree) = {
      val (fun, targs, argss) = decomposeApply(tree)
          
      val funEff = subtreeEffect(fun, env)
      val funEnv = env.applyEffect(funEff)
      val funLoc = funEff._3
      
      // foldLeft: we need to traverse left to right (that's the order in which effects
      // happen, the order of evaluation for the arguments).
      val (targsEff, targsEnv /*, targLocs*/) = (targs :\ (funEff, funEnv/*, List[Locality]()*/)) {
        case (targ, (eff, env/*, locs*/)) =>
          val e = subtreeEffect(targ, env)
          (sequence(eff, e), env.applyEffect(e)/*, e._3 :: locs*/)
      }
          
      val (argssEff, argssEnv, flatArgLocs) = (argss.flatten :\ (targsEff, targsEnv, List[Locality]())) {
        case (arg, (eff, env, locs)) =>
          val e = subtreeEffect(arg, env)
          (sequence(eff, e), env.applyEffect(e), e._3 :: locs)
      }
      
      // build a map from the function's parameter symbols to the localities of the arguments
      val flatParams = fun.symbol.tpe.paramss.flatten

      val locMap: Map[Location, Locality] = Map(ThisLoc(fun.symbol.owner) -> funLoc) ++ ((flatParams map SymLoc) zip flatArgLocs)
      
      withMap(locMap) { add(computeApplicationEffect(fun, targs, argss)) }
    }
    
    override def computeApplicationEffect(fun: Tree, targs: List[Tree] = Nil, argss: List[List[Tree]] = Nil) = {
      val latent = latentEffect(fun, targs, argss, rhsTyper.context1)
      val mappedLatent = adaptLatentEffect(latent, fun, targs, argss, rhsTyper.context1)
      val mappedPc = adaptToEffectPolymorphism(mappedLatent, fun, targs, argss, rhsTyper.context1)
      
      /* Effect polymorphism is not applied to the `@loc` effects, they are kept monomorphic. Example:
       * 
       *   def foo(a: A, b: B) @pc(a.bar(), b.baz()) = {
       *     a.bar()
       *     b.baz()
       *   }
       * 
       * Looking at the `@pc` effects, we cannot see the returned locality.
       * Maybe the `@loc` annotations can be extended in future to support something like
       * `@loc(b.baz())`.
       */
      (mappedPc._1, mappedPc._2, mappedLatent._3)
    }
  }
  
  private var currentMap: Map[Location, Locality] = null
  def withMap[T](map: Map[Location, Locality])(op: => T): T = {
    val savedMap = currentMap
    currentMap = map
    val res = op
    currentMap = savedMap
    op
  }

  override def adaptLatentEffect(eff: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    mapLocalities(eff, currentMap)
    
    /* @TODO this is not enough!!!
     *
     * If there are multiple assign / modification effects in `eff`, then these need to be
     * combined, the localities must be merged until reaching a fixpoint. For example
     * 
     *   def foo(a: A, b: B) = {
     *     a.store(b)
     *     b.modify()
     *   }
     * 
     * really???
     * (=> continue example: local environment that is modified by the two effects. does it always stay well-formed?)
     */
    
  }
    
  override def adaptPcEffect(eff: Elem, pc: PCInfo, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    /* Example: consider we treat the application of method `foo`, e.g.
     * 
     *   qual.foo(arg)
     * 
     * where
     *
     *   def foo(a: A) @pc(a.bar(_))
     *   class A { def bar(b: B) @mod(this) @mod(b) }
     * 
     * Then the arguments to `adaptPcEffect` are
     *   eff   = @mod(this) @mod(b)
     *   pc    = PCInfo(a, bar)
     *   fun   = qual.foo
     *   argss = (arg)
     * 
     * We have to map the localities of `@mod(this) @mod(b)`. The correct
     * locality map to apply is the following:
     * 
     *   this -> { localityOf(arg) }
     *   b    -> AnyLoc (or, just don't put b in the map)
     */
    val paramLoc = SymLoc(pc.param)
    // @TODO: fix when enabling PC calls on `this`
    val pcMap: Map[Location, Locality] = Map(ThisLoc(pc.fun.owner) -> currentMap.getOrElse(paramLoc, abort("parameter not in locations map: "+ paramLoc +", "+ currentMap)))
    mapLocalities(eff, pcMap)
  }

  def mapLocalities(eff: Elem, map: Map[Location, Locality]) = {
    val store = eff._1 match {
      case StoreAny => StoreAny
      case StoreLoc(effs) =>
        ((StoreLoc(): Store) /: effs) {
          case (store, (in, from)) =>
            val mappedFrom = mapLocality(from, map)
            var res = store
            map.getOrElse(in, nonMappedLocality(in)) match {
              case AnyLoc => StoreAny
              case LocSet(locs) =>
                for (loc <- locs) { res = res.include(loc, mappedFrom) }
            }
            res
        }
    }
    
    val assign = eff._2 match {
      case AssignAny(to) => AssignAny(mapLocality(to, map))
      case AssignLoc(strong, weak) =>
        val mapStrong = strong.map(e => (e._1, mapLocality(e._2, map)))
        val mapWeak = weak.map(e => (e._1, mapLocality(e._2, map)))
        AssignLoc(mapStrong, mapWeak)
    }
    
    val loc = mapLocality(eff._3, map)
      
    (store, assign, loc)
  }
    
  def mapLocality(loc: Locality, map: Map[Location, Locality]) = loc match {
    case AnyLoc => AnyLoc
    case LocSet(locs) =>
      ((LocSet(): Locality) /: locs)((set, loc) => joinLocality(set, map.getOrElse(loc, nonMappedLocality(loc))))
  }
    
  def nonMappedLocality(loc: Location): Locality = loc match {
    case SymLoc(s) =>
      if (isInScope(s)) LocSet(loc)
      else AnyLoc
    case ThisLoc(s) =>
      if (isInScope(s)) LocSet(loc)
      else AnyLoc
    case Fresh =>
      LocSet(loc)
  }
   
  def isInScope(s: Symbol): Boolean = true
}













