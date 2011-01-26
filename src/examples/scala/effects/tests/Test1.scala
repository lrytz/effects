package effects.tests

import annotation.effects._


class Test1 {
  def foo(x: Int): Int @pure = x + 1
}
