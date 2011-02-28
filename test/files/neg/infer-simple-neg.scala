import annotation.effects._
import simple._

class test {
  def f1: Int @refine = 1
  def v1: Int @noEff = f1

  def f2 = 1
  def v2: Int @noEff = f2

  def f3: Int @infer = { eff(); 1 }
  def v3: Int @noEff = f3

  def f4 = () => 1
  def v41: (() => Int) { def apply(): Int @noEff } = f4
  def v42: Int @noEff = f4()

  def f5: (() => Int) @infer @refine = () => { eff(); 1 }
  def v51: ((() => Int) { def apply(): Int @noEff }) @noEff = f5
  def v52: Int @noEff = f5()

  val v6: (() => Int) { def apply(): Int @noEff } = () => { eff(); 1 }

  val f71: (Int => Int => Int) @refine = (x: Int) => (y: Int) => x + y
  def f72(x: Int): (Int => Int) @refine @infer = f71(x)  // (Int)(Int => Int){def apply(x$1: Int): Int @eff} @noEff
  def f73(z: Int): Int @infer = f72(z)(10)               // (Int)Int @eff (because of +)
  def v71(x: Int): (Int => Int) @noEff = f72(x)          // no error, f72 has no latent effect
  def v72(): Int @noEff = f73(10)                        // error

  abstract class C8 { def f: Int }
  def f8: C8 @infer @refine = new C8 { def f: Int @infer = 1 }
  def v81: Int @noEff = f8.f    // error (`f8` has @eff, from constructor)
  def v82(c: C8): Int @noEff = c.f

  object o9 { val f: (() => Int) { def apply(): Int @eff } = () => 1 }
  val v9: (() => Int) { def apply(): Int @noEff } = o9.f

  def f101(x: Int): Int @infer = x
  def f102: Int @refine = f101(1)
  def v10: Int @noEff = f102
}
