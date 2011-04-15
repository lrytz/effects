package effects

import annotation.effects._; import simple._; import xio._; import exceptions._; import pc._

class Session {
  class A { def f() = 0 }
  def m(a: A): Int @infer = {
    def n: Int @infer = a.f()
    n
  }
}
