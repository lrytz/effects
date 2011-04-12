package scala.annotation.effects

package object xio {
  def doXio(): Unit @xio.xio @simple.noEff = ()
  def mask[T](action: => T): T @xio.noXio @simple.noEff = action
}
