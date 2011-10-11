package effects.tests

import annotation.effects._
import pc._
import state._

class Test1 {
  var x = 1
  def f(cond: Boolean, f: Int => Int): Unit @pure @mod(this) @pc(f.apply(%)) = {
    while (cond) {
      x = x + 1
      f(1)
    }
  }
}
