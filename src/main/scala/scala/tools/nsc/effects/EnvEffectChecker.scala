package scala.tools.nsc.effects
import collection.mutable.ListBuffer

abstract class EnvEffectChecker[L <: CompleteLattice] extends EffectChecker[L] {
  import global._
  import analyzer.{Typer, Context}

  import lattice.{Elem, toElemOps}
  import pcLattice.{AnyPC, PC, PCInfo, ThisLoc, ParamLoc}

  /**
   * @implement
   * 
   * Some effect checkers need to keep an effect typing environment while analyzing
   * side effects. This can be implemented by overriding this value with a custom
   * EffectEnv instance. See also documentation on EffectEnv
   */
  val effectEnv: EffectEnv[L] { val checker: EnvEffectChecker.this.type }
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
    
    case class Res(eff: Elem, env: Env, parts: List[Elem])
    implicit def tuple2Res(t: (Elem, Env))             = Res(t._1, t._2, List(t._1))
    implicit def tuple2Res(t: (Elem, Env, List[Elem])) = Res(t._1, t._2, t._3)
    
    def analyze(env: Env, tree: Tree): Res = {
      val eff = subtreeEffect(tree, env)
      (eff, env.applyEffect(eff))
    }
    
    def seq(initEnv: Env, trees: Tree*): Res = {
      val b = new ListBuffer[Elem]()
      val r = ((lattice.bottom, initEnv) /: trees) {
        case ((eff, env), tree) =>
          val res = analyze(env, tree)
          b += res.eff
          (eff u res.eff, res.env)
      }
      (r._1, r._2, b.toList)
    }
    
    
    def or(initEnv: Env, trees: Tree*): Res = {
      val b = new ListBuffer[Elem]()
      val e = (lattice.bottom /: trees) {
        case (eff, tree) =>
          val e = subtreeEffect(tree, initEnv)
          b += e
          eff u e
      }
      (e, initEnv.applyEffect(e), b.toList)
    }

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

      val funRes = qualEffect(fun, env)
      val targsRes = seq(funRes.env, targs: _*)
      val argssRes = seq(targsRes.env, argss.flatten: _*)

      val (latentEff, pcEffs) = computeApplicationEffect(fun, targs, argss, rhsTyper.context1)
      val adaptedLatent = adaptLatentEffect(latentEff, fun, targs, argss, ctx)
      val adaptedPcs = pcEffs.map(e => adaptPcEffect(e._1, e._2, ctx))
      
      val appEff = if (pcEffs.isEmpty) {
        adaptedLatent
      } else {
        combineLatentPc(adaptedLatent, adaptedPcs, argssRes.env)
      }

      add(funRes.eff u targsRes.eff u argssRes.eff u appEff)
    }    
  }

  /**
   * Combine the latent effect of a function with the effects that are due
   * to effect polymorphism.
   * 
   * Since we're in an effect system with environment, where the order of
   * effects matters (effects are applied in sequence to environments), there
   * is no generic way of combining effects.
   * 
   * At a function application, the `latent` and `pcs` effects have to be
   * combined in a worst-case way, because we don't know if they happen in
   * sequence, in parallel or even multiple times.
   * 
   * @TODO: example
   */
  def combineLatentPc(latent: Elem, pcs: List[Elem], env: Env): Elem
}