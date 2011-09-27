package scala.tools.nsc.effects
package state

import tools.nsc.Global
import collection.immutable.{Set, Map}

abstract class StateLattice extends CompleteLattice {
  val global: Global
  import global._
  import analyzer.Context


  type Elem = (Store, Assignment, Locality)

  /* Even though the effect for @pure is (StoreLoc(), AssignLoc(), AnyLoc), here we use
   * the real bottom. The reason is that the EffectChecker uses this as the initial value
   * when computing the effect of a method.
   */
  val bottom: Elem = (StoreLoc(), AssignLoc(), LocSet())
  val top: Elem = (StoreAny, AssignAny(AnyLoc), AnyLoc)

  override val pure: Elem = (StoreLoc(), AssignLoc(), AnyLoc)
  
  override implicit def toElemOps(eff: Elem) = new StateElemOps(eff)

  class StateElemOps(eff: Elem) extends ElemOps(eff) {
    def updateLocality(loc: Locality) = StateLattice.this.updateLocality(eff, loc)
  }
  
  /**
   * Construct effect elements form effects in one domain.
   */
  def mkElem(store: Store): Elem       = (store,      AssignLoc(), LocSet())
  def mkElem(assign: Assignment): Elem = (StoreLoc(), assign,      LocSet())
  def mkElem(loc: Locality): Elem      = (StoreLoc(), AssignLoc(), loc)

  /**
   * Change the returned locality of an effect, while making sure
   * that the result is a well-formed effect triple. Simply said,
   * a fresh value can only be returned by methods that don't have
   * any side-effects.
   * 
   * @TOOD: double-check this. is it correct?
   * also, in some cases we put the location to AnyLoc; is it only
   * here that we have to do so? or also in some places in the checker?
   */
  def updateLocality(eff: Elem, loc: Locality) = {
    if (loc.isFresh) {
      if (eff._1.isPure && eff._2.isPure)
        (eff._1, eff._2, loc)
      else if (eff._3.isFresh)
        (eff._1, eff._2, AnyLoc)
      else
        eff
    } else if (eff._1 == StoreAny) {
      (eff._1, eff._2, AnyLoc)
    } else {
      (eff._1, eff._2, loc)
    }
  }

  /**
   * Join effects, e.g. in
   * 
   *   if (..) { x = a } else { if (..) x = b }
   *   
   * the resulting effect is @assign(x, {a, b})
   */
  def join(a: Elem, b: Elem) =
    (joinStore(a._1, b._1), joinAssignment(a._2, b._2), joinLocality(a._3, b._3))

  def joinStore(a: Store, b: Store): Store = (a, b) match {
    case (StoreAny, _) | (_, StoreAny) =>
      StoreAny

    case (StoreLoc(as), StoreLoc(bs)) =>
      val merged = (Map[Location, LocSet]() /: as) {
        case (map, (location, aSet)) =>
          val res = bs.get(location).map(aSet.union).getOrElse(aSet)
          map + (location -> res)
      }
      val onlyInB = bs.filterNot(elem => as.contains(elem._1))
      StoreLoc(merged ++ onlyInB)
  }

  def joinAssignment(a: Assignment, b: Assignment): Assignment = (a, b) match {
    case (AssignAny(as), b) =>
      AssignAny(joinLocality(as, b.assignedLocality))
      
    case (a, AssignAny(bs)) =>
      AssignAny(joinLocality(a.assignedLocality, bs))
      
    case (AssignLoc(aEffs), AssignLoc(bEffs)) =>
      
      val merged = (Map[SymLoc, Locality]() /: aEffs) {
        case (map, (location, aLoc)) =>
          val res = bEffs.get(location).map(joinLocality(aLoc, _)).getOrElse(aLoc)
          map + (location -> res)
      }
      val res = merged ++ bEffs.filterNot(elem => merged.contains(elem._1))
      AssignLoc(res)
  }

  def joinLocality(a: Locality, b: Locality): Locality = (a, b) match {
    case (AnyLoc, _) | (_, AnyLoc) =>
      AnyLoc

    case (LocSet(as), LocSet(bs)) =>
      LocSet(as ++ bs)
  }


  /**
   * LTE
   */
  def lte(a: Elem, b: Elem) =
    lteStore(a._1, b._1) && lteAssignment(a._2, b._2) && lteLocality(a._3, b._3)

  def lteStore(a: Store, b: Store) = (a, b) match {
    case (_, StoreAny) => true
    case (StoreAny, _) => false
    case (StoreLoc(as), StoreLoc(bs)) =>
      as.forall({
        case (location, aSet) => bs.get(location).map(bSet => aSet.s.subsetOf(bSet.s)).getOrElse(false)
      })
  }
  
  def lteAssignment(a: Assignment, b: Assignment) = (a, b) match {
    case (a, AssignAny(bs)) => lteLocality(a.assignedLocality, bs)
    case (AssignAny(as), b) => false
    case (AssignLoc(aEffs), AssignLoc(bEffs)) =>
      aEffs.forall({
        case (location, aLoc) =>
          bEffs.get(location).map(bLoc => lteLocality(aLoc, bLoc)).getOrElse(false)
      })
  }
  
  def lteLocality(a: Locality, b: Locality) = (a, b) match {
    case (_, AnyLoc) => true
    case (AnyLoc, _) => false
    case (LocSet(as), LocSet(bs)) =>
      as.subsetOf(bs)
  }
    

  /**
   * Locality of returned value
   */
  trait Locality {
    def isFresh = this match {
      case LocSet(s) =>
        s.isEmpty || s.toList == List(Fresh)
      case _ => false
    }
    
    def filterOutOfScope(ctx: Context): Locality
  }
  case object AnyLoc extends Locality {
    def filterOutOfScope(ctx: Context) = AnyLoc
  }
  case class LocSet(s: Set[Location] = Set()) extends Locality {
    def this(l: Location) = this(Set(l))
    
    def union(b: LocSet) = LocSet(s union b.s)
    def add(loc: Location) = LocSet(s + loc)
    
    def filterOutOfScope(ctx: Context) = LocSet(s.filter(_.isInScope(ctx)))
  }
  object LocSet {
    def apply(l: Location): LocSet = new LocSet(l)
  }
  
  /**
   * Locations, places that are subject to modification effects.
   */
  sealed trait Location {
    def isLocalVar = this match {
      case SymLoc(sym) => sym.isLocal && sym.isVariable
      case ThisLoc(_) => false
      case Fresh => false
    }
    
    /**
     * Note the difference for parameters and local values / variables:
     *  - a local variable defined in a method is out of scope outside that method
     *  - however, parameters also have the method as owner, but they are still in
     *    scope outside the method.
     */
    def isInScope(ctx: Context): Boolean = this match {
      case Fresh => true
      case ThisLoc(_) => true
      case SymLoc(sym) =>
        if (sym.isParameter)
          localIsInScope(sym, ctx)
        else
          localIsInScope(sym, ctx.outer)
    }
  }
  case class SymLoc(sym: Symbol) extends Location {
    override def hashCode() = sym.hashCode
    override def equals(other: Any) = other match {
      case SymLoc(otherSym) => sym.owner == otherSym.owner && sym.name == otherSym.name
      case _ => false
    }
  }
  case class ThisLoc(sym: Symbol) extends Location
  case object Fresh extends Location
  
  
  /**
   * Is the local value / variable or paramter `local` in scope with
   * respect to context `ctx`?
   *
   * This is checked by looking at the owner of `ctx` and all owner
   * symbols of its `outer` contexts. If any of these symbols is the
   * same as the owner of `local`, then that local value is in scope
   * with respect to that context.
   * 
   * Note that this only works correctly for local values / variables
   * and parameters. Inherited fields can be in scope while only a
   * subclass is in the context chain, not the actual owner of the field.
   */
  def localIsInScope(local: Symbol, ctx: Context): Boolean = {
    def contextHasOwner(ctx: Context, owner: Symbol): Boolean = {
      ctx.owner == owner || (ctx.outer != ctx && contextHasOwner(ctx.outer, owner))
    }
    contextHasOwner(ctx, local.owner)
  }



  /**
   * State modifications
   */
  trait Store {
    def include(in: Location, from: Location): Store = include(in, LocSet(from))
    def include(in: Location, from: Locality): Store = this match {
      case StoreAny =>
        StoreAny
      case StoreLoc(effs) => from match {
        case AnyLoc => StoreAny
        case locs @ LocSet(_) =>
          StoreLoc(extendStoreMap(effs, in, locs))
      }
    }
    
    def isPure = this match {
      case StoreLoc(effs) =>
        effs.toList match {
          case Nil => true
          case List((in, from)) => in == Fresh && from.isFresh
          case _ => false
        }
      case _ => false
    }
  }
  case object StoreAny extends Store
  case class StoreLoc(effs: Map[Location, LocSet] = Map()) extends Store {
    def this(in: Location, from: LocSet) = this(Map(in -> from))
  }
  object StoreLoc {
    def apply(in: Location, from: LocSet) = new StoreLoc(in, from)
  }
  
  def extendStoreMap(map: Map[Location, LocSet], loc: Location, set: LocSet) =
    map.updated(loc, map.get(loc).map(set.union).getOrElse(set))

  /**
   * Assignments to local variables
   */
  trait Assignment {
    def assignedLocality: Locality
    def include(to: SymLoc, from: Locality) = this match {
      case AssignAny(to) =>
        AssignAny(joinLocality(to, from))
      case AssignLoc(effs) =>
        val res = effs.updated(to, effs.get(to).map(joinLocality(from, _)).getOrElse(from))
        AssignLoc(res)
    }
    
    def isPure = this match {
      case AssignLoc(effs) =>
        (effs.toList match {
          case Nil => true
          case List((loc, from)) => loc == Fresh && from.isFresh
          case _ => false
        })

      case _ => false
    }
  }
  case class AssignAny(to: Locality) extends Assignment {
    def assignedLocality = to
  } 

  case class AssignLoc(effs: Map[SymLoc, Locality] = Map()) extends Assignment {
    def this(to: SymLoc, from: Locality) = {
      this(Map(to -> from))
    }

    def assignedLocality = ((LocSet(): Locality) /: (effs.values))(joinLocality _)
  }
  object AssignLoc {
    def apply(to: SymLoc, from: Locality) = new AssignLoc(to, from)
  }
}
