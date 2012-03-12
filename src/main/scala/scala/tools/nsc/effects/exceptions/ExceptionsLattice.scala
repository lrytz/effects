package scala.tools.nsc.effects
package exceptions

import scala.tools.nsc._

abstract class ExceptionsLattice extends CompleteLattice {
  val global: Global
  import global._

  lazy val errorType = definitions.getRequiredClass("java.lang.Error").tpe
  lazy val runtimeExceptionType = definitions.getRequiredClass("java.lang.RuntimeException").tpe
  lazy val throwableType = definitions.ThrowableClass.tpe
  lazy val nothingType = definitions.NothingClass.tpe

  type Elem = List[Type]

  lazy val bottom = List(nothingType)
  lazy val top = List(throwableType)
  
  def join(a: Elem, b: Elem): Elem = a match {
    case Nil => b
    case _ => b match {
      case Nil => a
      case _ =>
        val unrelated = mask(a, b)
        unrelated ::: b
    }
  }

  def lte(a: Elem, b: Elem): Boolean =
    a.forall(ta => b.exists(tb => ta <:< tb))

  /**
   * Removes from `orig` those exception types that
   * are masked by `masked`. For example in
   * 
   *   E <: Exception
   *   E1 <: E
   *   F <: Exception
   *   
   *   mask(List(E1, F), List(E)) == List(F)
   */
  def mask(orig: Elem, masked: Elem): Elem =
    orig.filter(ex =>     // e.g: ex = IOException
      !masked.exists(m => //      m  = Exception
        ex <:< m))        //      since ex <:< m, remove ex

  /**
   * Removes from `elem` the unchecked exceptions.
   */
  def checked(elem: Elem): Elem =
    elem.filter(ex => !(ex <:< errorType || ex <:< runtimeExceptionType))
}
