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
  def empty = EnvMap()
  
  trait StateEnvImpl extends EnvImpl {
    
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
              // @TODO: could exclude the localities of assigned locations which are not in scope? should not happen!
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
            // if there are local variables, their locality can change over time, and the
            // environment would be not well formed.
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
    
    
    def mapLocations(map: Map[Location, Locality]): Env = this match {
        case AnyEnv =>
          AnyEnv
        case EnvMap(m, localsTo) =>
          // in m1 ++ m2, when a key exists in both maps, the value of m2 is picked.
          EnvMap(m ++ map, localsTo)
      }

    /**
     * Look up the locality of a location `loc` in the current environment.
     * 
     * The locality of a non-mapped location depends on the context, therefore
     * this method just returns `None` in that case. Have a look at the method
     * `selectedLocality` to see the default localities.
     *
     * Note that when analyzing the effect of a method, we start off with an
     * empty environment, where nothing is mapped, and `selectedLocality` uses
     * the default localities for everything.
     */
    def lookup(loc: Location): Option[Locality] = this match {
      case AnyEnv => Some(AnyLoc)
      case EnvMap(m, localsTo) =>
        if (localsTo.isDefined && loc.isLocalVar) {
          Some(localsTo.get)
        } else {
          loc match {
            case SymLoc(sym) =>
              // there can be multiple symbols for the same parameter.. see doc on sameParam
              m.find({
                case (SymLoc(s), _) => pcLattice.sameParam(s, sym)
                case _ => false
              }).map(_._2)
            case _ =>
              m.get(loc)
          }
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
}