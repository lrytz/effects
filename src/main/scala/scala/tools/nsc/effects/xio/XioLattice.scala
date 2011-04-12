package scala.tools.nsc.effects
package xio

class XioLattice extends CompleteLattice {
  type Elem = XioEffect

  def bottom = NoXio
  def top = Xio

  def join(a: Elem, b: Elem) = (a, b) match {
    case (NoXio, NoXio) => NoXio
    case _ => Xio
  }
  override def join(elems: Elem*) =
    if (elems.contains(Xio)) Xio
    else NoXio

  def lte(a: Elem, b: Elem) =
    a == NoXio || b == Xio
}

sealed trait XioEffect
case object Xio extends XioEffect
case object NoXio extends XioEffect
