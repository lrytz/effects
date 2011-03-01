package scala.annotation.effects

package object xio {
  def doXio(): Unit @xio.xio = ()
  def mask[T](action: => T): T @xio.noXio = action
}
