package scala.tools.nsc.effects
package state

import scala.tools.nsc._
import scala.collection.{immutable => i}
import pc._

class StateChecker(val global: Global) extends EffectChecker[StateLattice] with ConvertAnnots with PCTracking[StateLattice] {
  import global._
  import analyzer.Typer

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
     * The `@assign` effects are applied first, which is a conservative guess.
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
        case Apply(_, _) =>
          handleApplication(tree)
          
        case TypeApply(_, _) =>
          handleApplication(tree)
          
        case Select(_, _) =>
          if (tree.symbol.isMethod) {
            // applications to parameterless methods are `Select` trees, e.g. getters
            handleApplication(tree)
          } else {
            // TODO: handle selection of other things. (like what? objects, for instnace)
          }

        case Ident(name) =>
          // an Ident tree can refer to parameters, local values or packages in the `root` package.
          val sym = tree.symbol
          if (sym.owner.isRootPackage) mkElem(AnyLoc)
          else mkElem(LocSet(SymLoc(tree.symbol))) // @TODO: is this OK for local objects?


        case Assign(lhs, rhs) =>
          val lhsEffect = subtreeEffect(lhs, env)
          val lhsEnv = env.applyEffect(lhsEffect)
          
          val rhsEffect = subtreeEffect(rhs, lhsEnv)
          val rhsEnv = lhsEnv.applyEffect(rhsEffect)

          val parts = sequence(lhsEffect, rhsEffect)
          
          val lhsLoc = lhsEffect._3 match {
            case LocSet(s) =>
              assert(s.size == 1)
              s.toList(0)
          }
          
          val assignEff = mkElem(AssignLoc(lhsLoc, rhsEffect._3, true)) // @TOOD: don't do this if `lhsLoc` and `rhsEffect._3` are fresh
          val resEff = sequence(parts, assignEff)
          add((resEff._1, resEff._2, LocSet())) // no value is returned, so there's no locality

        case _ => ()
      }
        
    }

    def handleApplication(tree: Tree) = {
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

      
      val locMap: Map[Location, Locality] = Map((ThisLoc(fun.symbol.owner) -> funLoc)) ++ ((flatParams map SymLoc) zip flatArgLocs)
      val annots = fun.symbol.tpe.finalResultType.annotations
      val latentEffect = mapLocalities(fromAnnotation(annots).getOrElse(lattice.top), locMap)
      
      // todo: change localities! this -> receiver's locality, param symbol localities to argument localities
      

      val applyEffects = new collection.mutable.ListBuffer[Elem]()

      pcFromAnnotations(annots) match {
        case None | Some(AnyPC) =>
          // @TODO all effects from all methods reachable trough the parameters. (also, the
          // same thing has to be done in PCTracking, method anyParamCall)
          applyEffects += lattice.top
          
        case Some(PC(calls)) =>
          for (PCInfo(param, pcfun, pcargtpss) <- calls) {
            
            
            
            /* - find argument matching `param`
             * - find the argument's type
             * - find the type of `pcfun` as seen from the argumetnt type
             * - look at the effect
             * - replace the `this` locality with the argument locality
             * - replace all argument localities with `AnyLoc`
             *
             * - find nested PC's (recursively). In those, all localities are AnyLoc.
             *
             */
          }
      }

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
}













