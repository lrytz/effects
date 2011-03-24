package scala.annotation.effects
package exceptions

class throws[E <: Throwable] extends Effect
trait |[A <: Throwable, B <: Throwable] extends Throwable
