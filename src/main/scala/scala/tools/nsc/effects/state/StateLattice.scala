package scala.tools.nsc.effects
package state

import tools.nsc.Global
import collection.{immutable => i}

abstract class StateLattice extends CompleteLattice {
  val global: Global
  import global._

  type Elem = (State, Freshness)

  val bottom = (Mod(), Fresh) // @TODO: maybe Mod(Set()) ?? since this is the value we use for @pure ??
  val top = (ModAll, NonFresh)

  def join(a: Elem, b: Elem) =
    (joinState(a._1, b._1), joinFreshness(a._2, b._2))

  def joinFreshness(a: Freshness, b: Freshness) = (a, b) match {
    case (Fresh, Fresh) => Fresh
    case _ => NonFresh
  }

  def joinState(a: State, b: State) = (a, b) match {
    case (Mod(as), Mod(bs)) => Mod(as ++ bs)
    case (_, _) => ModAll
  }

  def lte(a: Elem, b: Elem) =
    lteState(a._1, b._1) && lteFreshness(a._2, b._2)

  def lteFreshness(a: Freshness, b: Freshness) =
    a == Fresh || b == NonFresh

  def lteState(a: State, b: State) = (a, b) match {
    case (_, ModAll) => true
    case (Mod(as), Mod(bs)) => as.subsetOf(bs)
    case (ModAll, _) => false
  }

  sealed abstract class State
//  case object Fresh extends State
  case class Mod(locations: i.Set[Symbol] = i.Set()) extends State
  case object ModAll extends State

  sealed abstract class Freshness
  case object Fresh extends Freshness
  case object NonFresh extends Freshness
}
