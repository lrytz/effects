package scala.tools.nsc.effects

trait EffectEnv[L <: CompleteLattice] {
  val lattice: L
  import lattice.{Elem, toElemOps}

  type Env <: EnvImpl
  def empty: Env
  def isTrivial: Boolean = false

  trait EnvImpl {
    def applyEffect(eff: Elem): Env

  }

  def seq(op1: Env => Elem, op2: Env => Elem, initEnv: Env): (Elem, Env) = {
    val eff1 = op1(initEnv)
    val env1 = initEnv.applyEffect(eff1)
    val eff2 = op2(env1)
    val env2 = env1.applyEffect(eff2)
    (eff1 u eff2, env2)
  }
  
  def or(op1: Env => Elem, op2: Env => Elem, initEnv: Env): (Elem, Env) = {
    val eff1 = op1(initEnv)
    val eff2 = op2(initEnv)
    val resEff = eff1 u eff2
    (resEff, initEnv.applyEffect(resEff))
  }
  
  def loop(op: Env => Elem, initEnv: Env): (Elem, Env) = {
    var resEff = lattice.bottom
    var resEnv = initEnv
    var eff = op(resEnv)
    while (eff != resEff) {
      resEnv = resEnv.applyEffect(eff)
      resEff = eff
      eff = op(resEnv)
    }
    (resEff, resEnv)
  }
}

class NoEffectEnv[L <: CompleteLattice] extends EffectEnv[L] {
  import lattice.Elem

  type Env = NoEnv.type
  def empty = NoEnv
  override val isTrivial: Boolean = true

  object NoEnv extends EnvImpl {
    def applyEffect(eff: Elem) = NoEnv
  }
}
