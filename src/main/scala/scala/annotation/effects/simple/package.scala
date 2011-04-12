package scala.annotation.effects

package object simple {
  def eff(): Unit @simple.eff @xio.noXio = ()
  def mask[T](action: => T): T @simple.noEff @xio.noXio = action
}
