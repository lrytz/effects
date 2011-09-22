package scala.tools.nsc.effects

/**
 * An effect environment allows to pass state through the effect analysis. The
 * side effects that are computed can depend on the environment. This allows
 * implementing effect system where the order of statements influences the
 * computed side-effect, for example
 * 
 *   doEffectOne()
 *   doEffectTwo()
 * 
 * can have a different effect than the two statements reversed, because the
 * effect of the first will change the environment used to analyze the second.
 * 
 * Note that there is no ordering in the side effects themselves (`lattice.Elem`
 * instances), the only operation to combine effects is to join them.
 */
abstract class EffectEnv[L <: CompleteLattice] {
  val checker: EffectChecker[L]
  import checker.lattice
  import lattice.{Elem, toElemOps}

  type Env <: EnvImpl
  def empty: Env

  trait EnvImpl {
    /**
     * Change this environment by applying the effect `eff`. Note that this method
     * has to conform to the following uniformity requirements:
     * 
     * 1. environments can only "grow" when effects are applied. The "size" of an
     *    environment is defined by the effect checking algorithm: analyzing the same
     *    code with a larger environment cannot result in a smaller effect. In other
     *    words, for all effects `eff`, trees `tree` and environments `env`, we have
     *    that
     * 
     *      computeEffect(tree, env) <= computeEffect(tree, env.applyEffect(eff))
     * 
     * 2. Applying two effects to an environment results in a smaller (or equal)
     *    environment as applying the join of the two effects, i.e.
     *    
     *      env.applyEffect(e1).applyEffect(e2) <= env.applyEffect(e1 u e2)
     *      env.applyEffect(e2).applyEffect(e1) <= env.applyEffect(e1 u e2)
     *    
     *    This implies the following:
     * 
     *    2.1. applying the `lattice.bottom` effect does not change the environment
     * 
     *    2.2 applying the same effect twice does not change the environment any further,
     *        i.e. `env.applyEffect(e).applyEffect(e)` is the same as `env.applyEffect(e)`.
     * 
     */
    def applyEffect(eff: Elem): Env
  }
}
