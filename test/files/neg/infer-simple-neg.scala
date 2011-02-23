import annotation.effects._
import simple._

class test {
  def f1: Int @refine = 1
  def v1: Int @noEff = f1
}
