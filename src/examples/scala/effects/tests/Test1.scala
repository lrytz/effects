package effects.tests

import annotation.effects._


class Test1 {
  var x = 1
  def foo(): Unit @pure = { x = 2 }
}
