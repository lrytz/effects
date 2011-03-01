import annotation.effects._
import simple._

class test1 {
  def f1: Int @infer = 1
  def v11: Int @noEff = f1
  def v12: Int @eff = f1

  def f2: Int @refine = 1
  def v2: Int @eff = f2

  def f3: Int @infer @refine = 1
  def v31: Int @noEff = f3
  def v32: Int @eff = f3

  def f4 = () => 1
  def v41: (() => Int) { def apply(): Int @eff } = f4

  def f5: (() => Int) @infer @refine = () => 1
  def v51: (() => Int) { def apply(): Int @noEff } = f5
  def v52: Int @noEff = f5()

  val v6: (() => Int) { def apply(): Int @eff } = () => { eff(); 1 }

  val f7: (Int => Int) @refine = (x: Int) => x
  def v7(x: Int): Int @noEff = f7(x)

  val f81: (Int => Int => Int) @refine = (x: Int) => (y: Int) => x
  def f82(x: Int): (Int => Int) @refine @infer = f81(x)
  def f83(x: Int): Int @infer = f82(x)(10)
  def v81(x: Int): ((Int => Int) { def apply(x: Int): Int @noEff } ) @noEff = f81(x) // f82 has no latent effect
  def v82(x: Int): Int @noEff = f83(x) // f83 has no latent effect

  abstract class C9 { def f: Int }
  val f9: C9 @refine = new C9 { def f: Int @infer = 1 }
  def v9: Int @noEff = f9.f
}

class test2 {
  object o1 { val f: (() => Int) { def apply(): Int @eff } = () => 1 }
  val v1: (() => Int) { def apply(): Int @eff } = o1.f

  def f21(x: Int): Int @infer = x
  def f22: Int @infer = f21(1)
  def v2: Int @noEff = f22

  private val f3 = () => 1
  val v3: (() => Int) { def apply(): Int @noEff } = f3
}

