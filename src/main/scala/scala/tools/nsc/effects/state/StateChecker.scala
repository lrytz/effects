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
            /* Take all local variables (var only, not val!) out of the map `m`, only keep the
             * location map for parameter symbols.
             * Set the `localsTo` accordingly: join of `to`, all localities of local variables
             * in `m`, and the current locality in `localsTo`.
             */
            val (localVarsMap, othersMap) = m.partition(e => e._1.isLocalVar)
            val assignedLocality = (to :: localVarsMap.map(_._2).toList).reduceRight(joinLocality)
            val resLocality = localsTo.map(l => joinLocality(l, assignedLocality)).orElse(Some(assignedLocality))
            EnvMap(othersMap, resLocality)
            
          case assgn @ AssignLoc(strong, weak) =>
            if (localsTo.isDefined) {
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

    def lookup(loc: Location) = this match {
      case AnyEnv => AnyLoc
      case EnvMap(m, localsTo) =>
        if (localsTo.isDefined && loc.isLocalVar) {
          localsTo.get
        } else {
          m.getOrElse(loc, LocSet(loc))
        }
    }
  }
  /**
   * `m` maps locations (params, local variables) to localities.
   * if `localsTo` is set, this defines the locality of all local variables (i.e. if
   * a `AssignAny(to)` effect occured).
   */
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

        case Select(qual, name) =>
          val sym = tree.symbol
          if (sym.isMethod) {
            // applications to parameterless methods are `Select` trees, e.g. getters
            handleApplication(tree)
          } else {
            // selection of an object or a field (inside a setter, fields are selected)
            val qualEff = subtreeEffect(qual, env)
            val qualEnv = env.applyEffect(qualEff)
            add((qualEff._1, qualEff._2, localityOf(sym, qualEnv, rhsTyper.context1)))
          }

        case Ident(name) =>
          val sym = tree.symbol
          if (sym.isMethod) {
            handleApplication(tree)
          } else {
            // an Ident tree can refer to parameters, local values or packages in the `root` package.
            if (sym.owner.isRootPackage) add(mkElem(AnyLoc))
            else add(mkElem(localityOf(sym, env, rhsTyper.context1))) // @TODO: is this OK for local objects? maybe instead of putting SymLoc for everything else, make specific tests for params, locals to create a SymLoc, and AnyLoc otherwise.
          }


        case Assign(lhs, rhs) =>
          val lhsEffect = subtreeEffect(lhs, env)
          val lhsEnv = env.applyEffect(lhsEffect)
          
          val rhsEffect = subtreeEffect(rhs, lhsEnv)
          // val rhsEnv = lhsEnv.applyEffect(rhsEffect) // not needed

          val parts = sequence(lhsEffect, rhsEffect)

          val lhsSymbol = lhsEffect._3 match {
            case LocSet(s) =>
              assert(s.size == 1)
              val SymLoc(sym) = s.toList(0)
              sym
          }
          
          val owner = lhsSymbol.owner
          val assignmnetEffect = if (owner.isClass) {
            // if the lefthand side is a selection of a field, then the assignment has a `@store` effect
            val loc = {
              if (owner.isModuleClass) SymLoc(owner.sourceModule)
              else ThisLoc(owner)
            }
            if (lhsSymbol.hasAnnotation(localClass)) {
              /* val List(List(arg)) = lhsSymbol.setter(owner).paramss
              (StoreLoc(loc, LocSet(SymLoc(arg))), AssignLoc(), LocSet()) */
              rhsEffect._3 match {
                case AnyLoc => mkElem(StoreAny)
                case from @ LocSet(_) => mkElem(StoreLoc(loc, from))
              }
            } else {
              mkElem(StoreLoc(loc, LocSet(Fresh)))
            }
          } else {
            // it's an assignment to a local variable, therefore an `@assign` effect
            mkElem(AssignLoc(SymLoc(lhsSymbol), rhsEffect._3, true)) // @TOOD: don't do this if `lhsLoc` and `rhsEffect._3` are fresh
          }
          
          val resEff = sequence(parts, assignmnetEffect)
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

    def qualEffect(tree: Tree, env: Env): Elem = tree match {
      case Select(qual, _) => subtreeEffect(qual, env)
      case Ident(_) => lattice.bottom
    }
    
    override def handleApplication(tree: Tree) {
      val (fun, targs, argss) = decomposeApply(tree)
      val funSym = fun.symbol
          
      val funEff = qualEffect(fun, env)
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
      val flatParams = funSym.tpe.paramss.flatten

      // @TODO: ThisLoc makes only sense when the owner is a class, not when it's a moduleclass (i.e. a method in an object)
      
      val locMap: Map[Location, Locality] = {
        val receiverMap = if (funSym.owner.isModuleClass) Map() else Map(ThisLoc(funSym.owner) -> funLoc)
        receiverMap ++ ((flatParams map SymLoc) zip flatArgLocs)
      }
      
      withMap(locMap) {
        val fromApp = computeApplicationEffect(fun, targs, argss) 
        val res = sequence(argssEff, fromApp)
        add((res._1, res._2, fromApp._3))
      }
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
    res
  }

  override def adaptLatentEffect(eff: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    mapLocalities(eff, currentMap, ctx)
    
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
    mapLocalities(eff, pcMap, ctx)
  }

  def mapLocalities(eff: Elem, map: Map[Location, Locality], ctx: Context) = {
    val store = eff._1 match {
      case StoreAny => StoreAny
      case StoreLoc(effs) =>
        ((StoreLoc(): Store) /: effs) {
          case (store, (in, from)) =>
            val mappedFrom = mapLocality(from, map, ctx)
            var res = store
            map.getOrElse(in, nonMappedLocality(in, ctx)) match {
              case AnyLoc =>
                res = StoreAny
              case LocSet(locs) =>
                for (loc <- locs) { res = res.include(loc, mappedFrom) }
            }
            res
        }
    }
    
    val assign = eff._2 match {
      case AssignAny(to) => AssignAny(mapLocality(to, map, ctx))
      case AssignLoc(strong, weak) =>
        val mapStrong = strong.map(e => (e._1, mapLocality(e._2, map, ctx)))
        val mapWeak = weak.map(e => (e._1, mapLocality(e._2, map, ctx)))
        AssignLoc(mapStrong, mapWeak)
    }
    
    val loc = mapLocality(eff._3, map, ctx)
      
    (store, assign, loc)
  }
    
  def mapLocality(loc: Locality, map: Map[Location, Locality], ctx: Context) = loc match {
    case AnyLoc => AnyLoc
    case LocSet(locs) =>
      ((LocSet(): Locality) /: locs)((set, loc) => joinLocality(set, map.getOrElse(loc, nonMappedLocality(loc, ctx))))
  }
    
  /**
   * The default locality when applying a locations-map to some location.
   */
  def nonMappedLocality(loc: Location, ctx: Context): Locality = loc match {
    case SymLoc(s) =>
      if (isInScope(s, ctx)) LocSet(loc)
      else AnyLoc
    case ThisLoc(s) =>
      if (isInScope(s, ctx)) LocSet(loc)
      else AnyLoc
    case Fresh =>
      LocSet(loc)
  }
  
  /**
   * Is the symbol `s` in scope with respect to context `ctx`?
   * This is checked by looking at the owner symbols of `s`. If one
   * of them is the same as the context's enclosing method, then
   * the symbol is in scope.
   */
  def isInScope(s: Symbol, ctx: Context): Boolean = {
    hasOwner(s, ctx.owner.enclMethod)
  }
  
  
  def hasOwner(s: Symbol, o: Symbol): Boolean = {
    if (s == NoSymbol) false
    else s == o || hasOwner(s.owner, o)
  }
  
  /**
   * The locality of a selected symbol.
   *  - if the symbol is a parameter of an outer method, SymLoc(sym)
   *  - if the symbol is a local value / variable defined in an outer method, SymLoc(sym)
   *  - if the symbol is a parameter of this method, then look up the locality in the environment
   *  - if the symbol is a local value / variable defined in the current method, then
   *    look up the locality in the environment
   *  - if the symbol is anything else, AnyLoc
   */
  def localityOf(sym: Symbol, env: Env, ctx: Context) = {
    val inCurrentMethod = hasOwner(sym, ctx.owner.enclMethod)
    
    val res = if ((sym.isParameter || sym.isLocal)) {
      if (!inCurrentMethod)
        LocSet(SymLoc(sym))
      else
        env.lookup(SymLoc(sym))
    } else {
      AnyLoc
    }
    println("locality of "+ sym +" is "+ res)
    res
  }
}
