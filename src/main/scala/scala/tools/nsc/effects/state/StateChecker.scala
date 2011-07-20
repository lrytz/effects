package scala.tools.nsc.effects
package state

import scala.tools.nsc._
import scala.collection.{immutable => i}

class StateChecker(val global: Global) extends EffectChecker[StateLattice] with ConvertAnnots {
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

  override def newEffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(tree, EnvMap(), typer, owner, unit)


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

  
  def computeEffect(tree: Tree, env: Env, typer: Typer, owner: Symbol, unit: CompilationUnit): Elem = {
    new StateTraverser(tree, env, typer, owner, unit).compute()
  }

  class StateTraverser(tree: Tree, env: Env, typer: Typer, owner: Symbol, unit: CompilationUnit) extends EffectTraverser(tree, typer, owner, unit) {
    def computeEffect(tree: Tree, newEnv: Env) = StateChecker.this.computeEffect(tree, newEnv, typer, owner, unit)

    override def traverse(tree: Tree) {
      tree match {
        case Ident(name) =>
          
        
        case Assign(lhs, rhs) =>
          val lhsEffect = computeEffect(lhs, env)
          val lhsEnv = env.applyEffect(lhsEffect)
          
          val rhsEffect = computeEffect(rhs, lhsEnv)
          val rhsEnv = lhsEnv.applyEffect(rhsEffect)

          val parts = sequence(lhsEffect, rhsEffect)
          
          val lhsLoc = lhsEffect._3 match {
            case LocSet(s) =>
              assert(s.size == 1)
              s.toList(0)
          }
          
          val assignEff = mkElem(AssignLoc(lhsLoc, rhsEffect._3, true))
          val resEff = sequence(parts, assignEff) 
          add((resEff._1, resEff._2, LocSet())) // no value is returned, so there's no locality

        case _ => ()
      }
        
    }
  }
}
