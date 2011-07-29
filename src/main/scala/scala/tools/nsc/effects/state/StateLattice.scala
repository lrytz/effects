package scala.tools.nsc.effects
package state

import tools.nsc.Global
import collection.immutable.{Set, Map}

abstract class StateLattice extends CompleteLattice {
  val global: Global
  import global._

  type Elem = (Store, Assignment, Locality)

  /* Even though the effect for @pure is (StoreLoc(), AssignLoc(), AnyLoc), here we use
   * the real bottom. The reason is that the EffectChecker uses this as the initial value
   * when computing the effect of a method.
   */
  val bottom: Elem = (StoreLoc(), AssignLoc(), LocSet())
  val top: Elem = (StoreAny, AssignAny(AnyLoc), AnyLoc)

  override val pure: Elem = (StoreLoc(), AssignLoc(), AnyLoc)
  
  /**
   * Construct effect elements form effects in one domain.
   */
  def mkElem(store: Store) = (store, AssignLoc(), LocSet())
  def mkElem(assign: Assignment) = (StoreLoc(), assign, LocSet())
  def mkElem(loc: Locality) = (StoreLoc, AssignLoc(), loc)

  /**
   * Join effects, e.g. in
   * 
   *   if (..) { x = a } else { if (..) x = b }
   *   
   * the resulting effect is @weakAssign(x, {a, b})
   */
  def join(a: Elem, b: Elem) =
    (joinStore(a._1, b._1), joinAssignment(a._2, b._2), joinLocality(a._3, b._3))

  /**
   * Sequence effects. For instance, in a block
   *   {
   *     x = a
   *     if (..) x = b
   *   }
   *
   * The effect is @strongAssign(x, {a, b})
   */
  def sequence(a: Elem, b: Elem) =
    (joinStore(a._1, b._1), sequenceAssignment(a._2, b._2), joinLocality(a._3, b._3))


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


  /**
   * Joining a strong and a weak assignment results in a weak assigment.
   */
  def joinAssignment(a: Assignment, b: Assignment): Assignment = (a, b) match {
    case (AssignAny(as), b) =>
      AssignAny(joinLocality(as, b.assignedLocality))
      
    case (a, AssignAny(bs)) =>
      AssignAny(joinLocality(a.assignedLocality, bs))
      
    case (AssignLoc(aStrong, aWeak), AssignLoc(bStrong, bWeak)) =>
      /* aStrong, aWeak, bStrong, bWeak: Map[Location, Locality]
       * 
       * Example: given
       *   a: AssignLoc(strong(x -> {a}),                     weak(y -> {b}))
       *   b: AssignLoc(strong(x -> {c}, y -> {d}, z -> {e}), weak(v -> {f}))
       *   
       *  - x is strong in both            => strong in the result, merge localities
       *  - y is weak in a                 => weak in the result, merge localities
       *  - z (strong) does not exist in a => weak in the result
       *  - v (weak) does not exist in a   => weak in the result
       *
       *  ==> AssignLoc(strong(x -> {a, c}), weak(y -> {b, d}, z -> {e}, v -> {f}))
       */
      
      val (strong, aBecomeWeak) = ((Map[Location, Locality](), Map[Location, Locality]()) /: aStrong) {
        case ((strong, weak), (location, aLoc)) =>
          bStrong.get(location) match {
            case Some(bLoc) => (strong + (location -> joinLocality(aLoc, bLoc)), weak)
            case None => (strong, weak + (location -> aLoc))
          }          
      }

      val aAllWeak = aWeak ++ aBecomeWeak
      val bAllWeak = bWeak ++ bStrong.filterNot(elem => strong.contains(elem._1))
      
      val mergedWeak = (Map[Location, Locality]() /: aAllWeak) {
        case (map, (location, aLoc)) =>
          val res = bAllWeak.get(location).map(joinLocality(aLoc, _)).getOrElse(aLoc)
          map + (location -> res)
      }
      
      val weak = mergedWeak ++ bAllWeak.filterNot(elem => mergedWeak.contains(elem._1))
      
      AssignLoc(strong, weak)
  }
  
  def sequenceAssignment(a: Assignment, b: Assignment): Assignment = (a, b) match {
    case (AssignAny(as), b) =>
      AssignAny(joinLocality(as, b.assignedLocality))
      
    case (a, AssignAny(bs)) =>
      AssignAny(joinLocality(a.assignedLocality, bs))

    case (AssignLoc(aStrong, aWeak), AssignLoc(bStrong, bWeak)) =>
      /* aStrong, aWeak, bStrong, bWeak: Map[Location, Locality]
       *
       * For each location:
       * 
       *   s = strong write
       *   w = weak write
       *   _ = no assign effect for that location
       * 
       *   | a | b || result               |
       *   +---+---++----------------------+
       *   | * | s || s with locality in b |
       *   | s | w || s, merge localities  | (1)
       *   | w | w || w, merge localities  | (2)
       *   | _ | w || w with locality in b | (3)
       *   | * | _ || as a                 | (1), (2)
       */
      
      val aStrongVisible = aStrong.filterNot(elem => bStrong.contains(elem._1))
      val aWeakVisible = aWeak.filterNot(elem => bStrong.contains(elem._1))
      
      // (1)
      val aStrongMerged = (Map[Location, Locality]() /: aStrongVisible) {
        case (map, (location, aLoc)) =>
          val res = bWeak.get(location).map(joinLocality(aLoc, _)).getOrElse(aLoc)
          map + (location -> res)
      }
      
      // (2)
      val aWeakMerged = (Map[Location, Locality]() /: aWeakVisible) {
        case (map, (location, aLoc)) =>
          val res = bWeak.get(location).map(joinLocality(aLoc, _)).getOrElse(aLoc)
          map + (location -> res)
      }
      
      // (3)
      val bWeakOnly = bWeak.filterNot(elem => aStrongMerged.contains(elem._1) || aWeakMerged.contains(elem._1))

      val strong = bStrong ++ aStrongMerged
      val weak = aWeakMerged ++ bWeakOnly
      
      AssignLoc(strong, weak)
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
  
  // strong update is smaller than weak update
  def lteAssignment(a: Assignment, b: Assignment) = (a, b) match {
    case (a, AssignAny(bs)) => lteLocality(a.assignedLocality, bs)
    case (AssignAny(as), b) => false
    case (AssignLoc(aStrong, aWeak), AssignLoc(bStrong, bWeak)) =>
      aStrong.forall({
        case (location, aLoc) =>
          bStrong.get(location).map(bLoc => lteLocality(aLoc, bLoc)).getOrElse({
            bWeak.get(location).map(bLoc => lteLocality(aLoc, bLoc)).getOrElse(false)
          })
      }) &&
      aWeak.forall({
        case (location, aLoc) =>
          bWeak.get(location).map(bLoc => lteLocality(aLoc, bLoc)).getOrElse(false)
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
  trait Locality
  case object AnyLoc extends Locality
  case class LocSet(s: Set[Location] = Set()) extends Locality {
    def this(l: Location) = this(Set(l))
    
    def union(b: LocSet) = LocSet(s union b.s)
/*
    def diff(b: LocSet) = LocSet(s diff b.s)
    def intersect(b: LocSet) = LocSet(s intersect b.s)
*/
  }
  object LocSet {
    def apply(l: Location): LocSet = new LocSet(l)
  }

  // will maybe be useful
  /* implicit def set2LocSet(s: Set[Location]) = new LocSet(s) */
  
  /**
   * Locations, places that are subject to modification effects.
   */
  trait Location {
    def isLocalVar = this match {
      case SymLoc(sym) => !sym.isParameter && sym.isVariable
      case ThisLoc(_) => false
      case Fresh => false
    }
  }
  case class SymLoc(sym: Symbol) extends Location
  case class ThisLoc(sym: Symbol) extends Location
  case object Fresh extends Location
  

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
/*          val res = effs.updated(in, effs.get(in).map(locs.union).getOrElse(locs))
          StoreLoc(res)*/
          StoreLoc(extendStoreMap(effs, in, locs))
      }
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
    def include(to: Location, from: Locality, useStrong: Boolean) = this match {
      case AssignAny(to) =>
        AssignAny(joinLocality(to, from))
      case AssignLoc(strong, weak) =>
        val m = if (useStrong) strong else weak
        val res = m.updated(to, m.get(to).map(joinLocality(from, _)).getOrElse(from))
        if (useStrong) AssignLoc(res, weak) else AssignLoc(strong, res)
    }
  }
  case class AssignAny(to: Locality) extends Assignment {
    def assignedLocality = to
  }
  case class AssignLoc(strong: Map[Location, Locality] = Map(), weak: Map[Location, Locality] = Map()) extends Assignment {
    def this(to: Location, from: Locality, useStrong: Boolean) = {
      this(if (useStrong) Map(to -> from) else Map(), if (useStrong) Map() else Map(to -> from))
    }

    def assignedLocality = ((LocSet(): Locality) /: (strong.values ++ weak.values))(joinLocality _)
  }
  object AssignLoc {
    def apply(to: Location, from: Locality, useStrong: Boolean) = new AssignLoc(to, from, useStrong)
  }
}
