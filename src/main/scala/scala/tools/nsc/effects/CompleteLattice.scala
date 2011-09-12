package scala.tools.nsc.effects

/**
 * @author Lukas Rytz
 * @version 0.1
 */
trait CompleteLattice {
  type Elem

  def bottom: Elem
  def top: Elem
  
  /**
   * This element is used for methods with a `@pure` annotation, and by default also
   * for getters and setters. For some effect systems, this value might be different
   * from `bottom`, see StateLattice for example.
   */
  def pure: Elem = bottom

  implicit def toElemOps(eff: Elem) = new ElemOps(eff)
  
  class ElemOps(eff: Elem) {
    def <= (other: Elem): Boolean = lte(eff, other)
  }
  

  def join(a: Elem, b: Elem): Elem
  def join(elems: Elem*): Elem = {
    if (elems.isEmpty) bottom
    else {
      var acc = bottom
      for (e <- elems) { acc = join(acc, e) }
      acc
    }
  }

  /**
   * Compare two effects, return `true` if `a` is smaller or equal to `b`
   */
  def lte(a: Elem, b: Elem): Boolean
}
