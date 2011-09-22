package scala.tools.nsc.effects
package state

abstract class StateEnv extends EffectEnv[StateLattice] {
  val checker: StateChecker
  import checker.{lattice, pcLattice}  
  import lattice.{Locality, AnyLoc, LocSet,
                  Location, SymLoc, Fresh, ThisLoc,
                  Store, StoreAny, StoreLoc,
                  Assignment, AssignAny, AssignLoc,
                  Elem, toElemOps,
                  joinLocality}

  type Env = StateEnvImpl
  def empty: Env = LocalEnv()
  
  sealed trait StateEnvImpl extends EnvImpl {
    
    /**
     * @TODO: show some documentation, some examples
     * 
     */
    def applyEffect(eff: Elem): Env = this match {
      case AnyEnv =>
        AnyEnv
        
      case LocalEnv(merged, locals) =>
        eff._1 match {
          case StoreAny =>
            AnyEnv
          case StoreLoc(effs) =>
            val resMerged = (merged /: effs) {
              case (locSets, (in, from)) =>
                val newLocs = (from.s + in).filterNot(_ == Fresh)
                if (newLocs.isEmpty) locSets // maybe not needed
                else {
                  val (unrelated, overlapping) = locSets.partition(set => set.s intersect newLocs isEmpty)
                  val merge = (newLocs /: overlapping) {
                    case (acc, overlapSet) => acc.union(overlapSet.s)
                  }
                  unrelated + LocSet(merge)
                }
            }
            
            val resLocals = locals match {
              case AnyLocals(to) =>
                AnyLocals(joinLocality(to, eff._2.assignedLocality))
                
              case Locals(map) => eff._2 match {
                case AssignAny(to) =>
                  val mapValues = map.map(_._2).reduceRight(joinLocality)
                  AnyLocals(joinLocality(to, mapValues))
                  
                case AssignLoc(effs) =>
                  val resMap = (map /: effs) {
                    case (m, (to, from)) =>
                      val res = m.get(to).map(joinLocality(_, from)).getOrElse(from)
                      m.updated(to, res)
                  }
                  Locals(resMap)
              }
            }

            LocalEnv(resMerged, resLocals)
        }
    }
    
    def lookup(loc: Location): Locality = this match {
      case AnyEnv => AnyLoc
      case LocalEnv(merged, locals) =>
        val fromMerge = merged.find(_.s.contains(loc)).getOrElse(LocSet(loc))
        if (!loc.isLocalVar) fromMerge
        else {
          locals match {
            case AnyLocals(to) => joinLocality(fromMerge, to)
            case Locals(map) =>
              map.get(loc).map(joinLocality(_, fromMerge)).getOrElse(fromMerge)
          }
        }
    }
  }

  /**
   * `merged` contains sets of locations that have been merged. Two locations become merged
   * when storing a value of one in another, for example
   * 
   *   def f(a: A, b: B) {
   *     a.store(b)    // LocalEnv after that statement: Set(Set(a, b))
   *   }
   * 
   * `localsEnv` represents the state of local variables, i.e. the locations they might
   * point to. For example:
   * 
   *   def f(a: A, b: B, c: C) {
   *     var x = a                     // Locals(x -> {a})
   *     def inner(): @assign(x, c) {
   *       var y = b                   // Locals(y -> {b})
   *       y = x                       // Locals(y -> {b, x})
   *       x = c                       // Locals(y -> {b, x}, x -> {c})
   *     }
   *     inner()                       // Locals(x -> {a, c})
   *     
   *   }
   * 
   * Note that local variables can also appear in merged sets. When computing the locality
   * of an "Ident", the merged sets and the locals have to be considered, i.e. given the env
   * 
   *   LocalEnv(SetSet((a, x)), Locals(x -> {a, b}))
   * 
   * the locality of "a" is {a, x}. The locality of "x" is {x, a, b}.
   * 
   * 
   * When there is an assignment effect to any vairable (AssignAny(to)), the locals map
   * represented by an AnyLocals instance with the apropriate target locality.
   */
  case class LocalEnv(merged: Set[LocSet] = Set(), locals: LocalsEnv = Locals()) extends Env
  case object AnyEnv extends Env
  
  sealed trait LocalsEnv
  case class Locals(map: Map[Location, Locality] = Map()) extends LocalsEnv
  case class AnyLocals(assignedTo: Locality) extends LocalsEnv
}