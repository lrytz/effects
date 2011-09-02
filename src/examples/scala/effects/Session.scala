package effects

import annotation.effects._
import pc._
import state._

class Test {
  def foo(c: Counter): Int @pure = {
    c.inc();
    c.get()
  }
}

@pure class Counter {
  private var i = 0
  def inc(): Unit @mod(this) = { i += 1 }
  def get(): Int @pure = i
}
