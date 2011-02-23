import annotation.effects._
import simple._

class test {
  def f1: Int @infer = 1
  def v11: Int @noEff = f1
  def v12: Int @eff = f1

  def f2: Int @refine = 1
  def v2: Int @eff = f2

  def f3: Int @infer @refine = 1
  def v31: Int @noEff = f3
  def v32: Int @eff = f3
}
