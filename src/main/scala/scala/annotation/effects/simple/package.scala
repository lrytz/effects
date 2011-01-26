package scala.annotation.effects

package object simple {
  def eff(): Unit @simple.eff = ()
  def mask[T](action: => T): T @simple.noEff = action
}
