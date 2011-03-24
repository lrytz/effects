package scala.annotation.effects

package object pc {
  /**
   * This value can be used for specifying a type in an annotation, e.g.
   *   @pc(m.foo(% : Int, % : String))
   */
  def % : Nothing = throw new Error("~ should never be called")
}
