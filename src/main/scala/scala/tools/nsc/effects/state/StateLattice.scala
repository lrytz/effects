package scala.tools.nsc.effects
package state

import tools.nsc.Global
import collection.{immutable => i}

abstract class StateLattice extends CompleteLattice {
  val global: Global
  import global._

  type Elem = State

  val bottom = Fresh // @TODO: maybe Mod(Set()) ?? since this is the value we use for @pure ??
  val top = ModAll

  def join(a: Elem, b: Elem) = (a, b) match {
    case (Fresh, Fresh) => Fresh
    case (a, Fresh) => a
    case (Fresh, b) => b
    case (ModAll, _) => ModAll
    case (_, ModAll) => ModAll
    case (Mod(as), Mod(bs)) => Mod(as ++ bs)
  }

  def lte(a: Elem, b: Elem) = (a, b) match {
    case (Fresh, _) | (_, ModAll) => true
    case (_, Fresh) | (ModAll, _) => false
    case (Mod(as), Mod(bs)) => as.subsetOf(bs)
  }

  sealed abstract class State
  case object Fresh extends State
  case class Mod(locations: i.Set[Symbol]) extends State
  case object ModAll extends State
}
