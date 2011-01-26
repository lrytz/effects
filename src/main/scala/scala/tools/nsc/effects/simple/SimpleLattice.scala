package scala.tools.nsc.effects
package simple


class SimpleLattice extends CompleteLattice {
  type Elem = SimpleEffect

  def bottom = NoEff
  def top = Eff

  def join(a: Elem, b: Elem) = (a, b) match {
    case (NoEff, NoEff) => NoEff
    case _ => Eff
  }
  override def join(elems: Elem*) =
    if (elems.contains(Eff)) Eff
    else NoEff

  def lte(a: Elem, b: Elem) =
    a == NoEff || b == Eff
}

sealed trait SimpleEffect
case object Eff extends SimpleEffect
case object NoEff extends SimpleEffect
