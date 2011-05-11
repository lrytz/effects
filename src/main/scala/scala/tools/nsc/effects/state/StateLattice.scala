package scala.tools.nsc.effects
package state

import tools.nsc.Global
import collection.{immutable => i}

abstract class StateLattice extends CompleteLattice {
  val global: Global
  import global._

  type Elem = (State, Locality)

  val bottom = (Mod(), Loc()) // @TODO: maybe (Mod(), NonLoc) ?? since this is the value we use for @pure ??
  val top = (ModAll, NonLoc)

  def join(a: Elem, b: Elem) =
    (joinState(a._1, b._1), joinLocality(a._2, b._2))

  def joinLocality(a: Locality, b: Locality) = (a, b) match {
    case (Loc(as), Loc(bs)) => Loc(as ++ bs)
    case _ => NonLoc
  }

  def joinState(a: State, b: State) = (a, b) match {
    case (Mod(as), Mod(bs)) => {
      // @modIfLoc(a, b) | @mod(a)  ==>  @modIfLoc(a, b)
      val (_, takeAs) = as.partition(a => a.param == None && bs.exists(_.location == a.location))
      val (_, takeBs) = bs.partition(b => b.param == None && takeAs.exists(_.location == b.location))
      Mod(takeAs ++ takeBs)
    }
    case (_, _) => ModAll
  }

  def lte(a: Elem, b: Elem) =
    lteState(a._1, b._1) && lteLocality(a._2, b._2)

  def lteLocality(a: Locality, b: Locality) = (a, b) match {
    case (_, NonLoc) => true
    case (Loc(as), Loc(bs)) => as.subsetOf(bs)
    case (NonLoc, _) => false
  }

  def lteState(a: State, b: State) = (a, b) match {
    case (_, ModAll) => true
    case (Mod(as), Mod(bs)) => as.forall(a => bs.exists(b => a.lte(b)))
    case (ModAll, _) => false
  }

  sealed abstract class State
  case class Mod(locations: i.Set[ModIfLoc] = i.Set()) extends State {
    def this(location: Symbol) = this(i.Set(ModIfLoc(location)))
  }
  case object ModAll extends State

  case class ModIfLoc(location: Symbol, param: Option[Symbol] = None) {
    def lte(o: ModIfLoc) = {
      location == o.location &&
      (param.isEmpty || (!o.param.isEmpty && param.get == o.param.get))
    }
  }

  sealed abstract class Locality
  case class Loc(locations: i.Set[Symbol] = i.Set()) extends Locality
  case object NonLoc extends Locality
}
