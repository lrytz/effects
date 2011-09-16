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
    val refinedRhs = refine(primConstrRhs, primConstrTyper, primConstrSym, unit)
    val refinedImpl = refine(impl, implTyper, classSym, unit)
    
    val env = effectEnv.empty
    
    val rhsEff = newEnvEffectTraverser(refinedRhs, env, primConstrTyper, primConstrSym, unit).compute()
    val implEff = newEnvEffectTraverser(refinedImpl, env.applyEffect(rhsEff), implTyper, classSym, unit).compute()

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
    
    case class Res(eff: Elem, env: Env)
    implicit def tuple2Res(t: (Elem, Env)) = Res(t._1, t._2)
    
    def analyze(env: Env, tree: Tree): Res = {
      val eff = subtreeEffect(tree, env)
      (eff, env.applyEffect(eff))
    }
    
    def seq(initEnv: Env, trees: Tree*): Res = {
      ((lattice.bottom, initEnv) /: trees) {
        case ((eff, env), tree) =>
          val res = analyze(env, tree)
          (eff u res.eff, res.env)
      }
    }
    
    
    def or(initEnv: Env, trees: Tree*): Res = {
      val e = (lattice.bottom /: trees) {
        case (eff, tree) =>
          val e = subtreeEffect(tree, initEnv)
          eff u e
      }
      (e, initEnv.applyEffect(e))
    }

    /* @TODO: probably we don't even need that, because applying (e1 u e2) to an environment
     * already gives the most conservative resulting environment
     * 
     */
/*    def loop(initEnv: Env, tree: Tree): Res = {
      var resEff = lattice.bottom
      var resEnv = initEnv
      var eff = subtreeEffect(tree, resEnv)
      while (eff != resEff) {
        resEff = eff
        resEnv = resEnv.applyEffect(eff)
        eff = subtreeEffect(tree, resEnv)
      }
      (resEff, resEnv)
    }*/

    override def traverse(tree: Tree) {
      tree match {
        case Block(stats, expr) =>
          val statsRes = seq(env, stats: _*)
          val exprRes = analyze(statsRes.env, expr)
          add(statsRes.eff u exprRes.eff)
          
        /* @TODO: CaseDef, Alternative, Sar, Bind, UnApply, ArrayValue, */
          
        case Assign(a, b) =>
          add(seq(env, a, b).eff)
        
        case If(cond, thenExpr, elseExpr) =>
          val condRes = analyze(env, cond)
          val thenElseRes = or(condRes.env, thenExpr, elseExpr)
          add(condRes.eff u thenElseRes.eff)
          
        /* @TODO: Match */
        
        case Try(block, catches, finalizer) =>
          val blockRes = analyze(env, block)
          // @TODO: catches. the patterns happen in sequence, but the pattern bodies we can treat as `or`, as only one of them gets executed.
          val finRes = analyze(blockRes.env, finalizer)
          add(blockRes.eff u finRes.eff)

        case _ =>
          super.traverse(tree)
      }
    }
    

    def qualEffect(tree: Tree, env: Env): Res = tree match {
      case Select(qual, _) => analyze(env, qual)
      case Ident(_) => (lattice.bottom, env)
    }

    override def handleApplication(tree: Tree) {
      val (fun, targs, argss) = decomposeApply(tree)
      val funSym = fun.symbol
      val ctx = rhsTyper.context1

      def adaptEffs(latent: Elem, pcs: List[(Elem, PCInfo)]) = {
        var res = adaptLatentEffect(latent, fun, targs, argss, ctx)
        for ((pcEff, pcInfo) <- pcs)
          res = res u adaptPcEffect(pcEff, pcInfo, ctx)
        res
      }
      
      val funRes = qualEffect(fun, env)
      val targsRes = seq(funRes.env, targs: _*)
      val argssRes = seq(targsRes.env, argss.flatten: _*)

      val (latentEff, pcEffs) = computeApplicationEffect(fun, targs, argss, rhsTyper.context1)
      

      val appEff = if (pcEffs.isEmpty) {
        withEnv(argssRes.env) { adaptLatentEffect(latentEff, fun, targs, argss, ctx) }
      } else {
        var prevRes = withEnv(argssRes.env) { adaptEffs(latentEff, pcEffs) }
        var appEnv = argssRes.env.applyEffect(prevRes)
        var res = withEnv(appEnv) { adaptEffs(latentEff, pcEffs) }
        while (!(res <= prevRes)) {
          prevRes = res
          appEnv = appEnv.applyEffect(prevRes)
          res = withEnv(appEnv) { adaptEffs(latentEff, pcEffs) }
        }
        res
      }

      add(funRes.eff u targsRes.eff u argssRes.eff u appEff)
    }    
  }
  
  /**
   * This vairable makes the current environment available during
   * `computeApplicationEffect`. This method calls `adaptLatentEffect`
   * and `adaptPcEffect`, which can be overridden to adapt the effects
   * on a function to the current environment.
   * 
   * For an example, see the implementation of StateChecker.
   */
  private var _currentEnv: Env = _ // effectEnv.empty (does not work, creates initialization deadlock)
  def currentEnv = _currentEnv
  def withEnv[T](env: Env)(op: => T): T = {
    val savedEnv = _currentEnv
    _currentEnv = env
    val res = op
    _currentEnv = savedEnv
    res
  }
}