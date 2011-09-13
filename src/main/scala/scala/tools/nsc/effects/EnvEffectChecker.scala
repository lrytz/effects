package scala.tools.nsc.effects

abstract class EnvEffectChecker[L <: CompleteLattice] extends EffectChecker[L] {
  import global._
  import analyzer.{Typer, Context}

  import lattice.{Elem, toElemOps}
  import pcLattice.{AnyPC, PC, PCInfo, ThisLoc, ParamLoc, sameParam}

  /**
   * @implement
   * 
   * Some effect checkers need to keep an effect typing environment while analyzing
   * side effects. This can be implemented by overriding this value with a custom
   * EffectEnv instance. See also documentation on EffectEnv
   */
  val effectEnv: EffectEnv[L] { val checker: EnvEffectChecker.this.type } /*= new NoEffectEnv[L] {
    val checker: EnvEffectChecker.this.type = EnvEffectChecker.this
  }*/
  import effectEnv.Env
  
  
  override def computeEffect(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) = {
    val refinedTree = refine(rhs, rhsTyper, sym, unit)
    newEnvEffectTraverser(refinedTree, effectEnv.empty, rhsTyper, sym, unit).compute()
  }

  override def computePrimConstrEffect(impl: Template, implTyper: Typer, classSym: Symbol,
                                       primConstrRhs: Tree, primConstrTyper: Typer, primConstrSym: Symbol,
                                       unit: CompilationUnit): Elem = {
    // @TODO: use environments!
    
    val refinedRhs = refine(primConstrRhs, primConstrTyper, primConstrSym, unit)
    val refinedImpl = refine(impl, implTyper, classSym, unit)
    
    val rhsEff = newEffectTraverser(refinedRhs, primConstrTyper, primConstrSym, unit).compute()
    val implEff = newEffectTraverser(refinedImpl, implTyper, classSym, unit).compute()

    rhsEff u implEff
  }


  override final def newEffectTraverser(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    newEnvEffectTraverser(rhs, effectEnv.empty, rhsTyper, sym, unit)
  
  /**
   * @implement
   * 
   * Instead of overriding "newEffectTransformer", an effect checker with an
   * environment will override this method.
   */
  def newEnvEffectTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    new EnvEffectTraverser(rhs, env, rhsTyper, sym, unit)

  
  class EnvEffectTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends EffectTraverser(rhs, rhsTyper, sym, unit) {
    /**
     * Computes the effect of a subtree of `rhs`.
     */
    def subtreeEffect(tree: Tree, env: Env): Elem = {
      newEnvEffectTraverser(tree, env, rhsTyper, sym, unit).compute()
    }

    def seq(initEnv: Env, trees: Tree*): (Elem, Env) = {
      ((lattice.bottom, initEnv) /: trees) {
        case ((eff, env), tree) =>
          val e = subtreeEffect(tree, env)
          (eff u e, env.applyEffect(e))
      }
    }
    
    def or(initEnv: Env, trees: Tree*): (Elem, Env) = {
      val e = (lattice.bottom /: trees) {
        case (eff, tree) =>
          val e = subtreeEffect(tree, initEnv)
          eff u e
      }
      (e, initEnv.applyEffect(e))
    }

    def loop(initEnv: Env, tree: Tree): (Elem, Env) = {
      var resEff = lattice.bottom
      var resEnv = initEnv
      var eff = subtreeEffect(tree, resEnv)
      while (eff != resEff) {
        resEff = eff
        resEnv = resEnv.applyEffect(eff)
        eff = subtreeEffect(tree, resEnv)
      }
      (resEff, resEnv)
    }

    override def traverse(tree: Tree) {
      tree match {
        case Block(stats, expr) =>
          val statsEff = seq(stats, env)
          seq(expr, statsEff)
          
          
        case If(cond, thenExpr, elseExpr) =>
          seq(env, cond, or(thenExpr, elseExpr))
          

          analyze(cond) >>= (res => {
            
          })
          
          
          val condEff = subtreeEffect(cond, env)
          val condEnv = env.applyEffect(condEff)
          
          val thenEff = subtreeEffect(thenExpr, condEnv)
          val elseEff = subtreeEffect(elseExpr, condEnv)
          
          val resEff = sequence(condEff, join(thenEff, elseEff))
          add(resEff)
          
/*          val (statsEff, statsEnv) = ((lattice.bottom, env) /: stats) {
            case ((eff, env), stat) =>
              val e = subtreeEffect(stat, env)
              (eff u e, env.applyEffect(e))
          }
          
          val exprEff = subtreeEffect(expr, statsEnv)
          add(sequence(statsEff, exprEff))
*/
      }
    }
  }
}