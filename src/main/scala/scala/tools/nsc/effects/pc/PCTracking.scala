/*
package scala.tools.nsc.effects
package pc

trait PCTracking[L <: CompleteLattice] extends EffectChecker[L] with ExternalPCEffects[L] { /* this: EffectChecker[L] => */
  import global._
  import analyzer.Context

  val pcCommons = new PCCommons {
    val global: PCTracking.this.global.type = PCTracking.this.global
  }
  import pcCommons._
  import pcLattice.{PCElem, PC, PCInfo, AnyPC, sameParam}
  
  import lattice.Elem

  
  override def adaptToEffectPolymorphism(latent: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = fun match {
    
    /* If the receiver of the function is a parameter then it's a parameter call. Therefore
     * we can ignore the effect, it is represented by the @pc annotation (which is already
     * present from the PCChecker phase). Example:
     * 
     *   def foo(a: A): B @pc(a.bar) = a.bar
     * 
     * The side-effect of the application `a.bar` does not have to be annotated, it's covered
     * by the `@pc(a.bar)` annotation.
     */
    case Select(id @ Ident(_), _) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
      lattice.bottom

    case _ =>
      var res = latent

      val flatArgss = argss.flatten
      val flatParamss = fun.symbol.tpe.paramss.flatten

      pcEffect(fun.symbol) match {
        case None | Some(AnyPC) =>
          res = lattice.join(res, anyParamCall(flatArgss, ctx))
        case Some(PC(calls)) =>
          var includedFuns = Set[Symbol]()
          
          for (pcInfo @ PCInfo(param, pcfun, pcargtpss) <- calls) {
            if (isParam(param, ctx.owner.enclMethod)) {
              /* The receiver of the paramCall is a parameter in the current context. Then we don't
               * need to consider its effect, instead the @pc annotation will be forwarded (done by
               * PCChecker). Example
               * 
               *   def m(a: A): R @pc(a.f()) = { def n() = a.f(); n() }
               * 
               * In the call to n(), there's a @pc(a.f()), but "a" is a param when calling n.
               */
              ()
            } else {
              // @TODO: implement param calls on `this`, i.e. @pc(this.bar())

              // sameParam compares name and owner. why: see its comment.
              val i = flatParamss.indexWhere(sameParam(_, param))
              assert(i >= 0)
              flatArgss(i) match {
                case id @ Ident(_) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
                  /* The argument expression is an `Ident` to another parameter. Then we don't have
                   * to expand the pc effect, instead it will be transformed into a pc effect (done
                   * by the PCChecer). Example
                   * 
                   *   def m(a1: A): C @pc(a1.foo) = { a.foo() }
                   *   def g(a2: A): C @pc(a2.foo) = { m(a1) }
                   * 
                   * In the call m(a1), m's @pc effect is not expanded.
                   */
                  ()
                case arg =>
                  /* Include the effect of a parameter call. The effect might be more specific than
                   * the effect of the `pcfun` symbol, in case that symbol is refined / overridden
                   * in the actual type of arg. Example:
                   * 
                   *   pcfun = Function1.apply
                   *   arg = (x => x + 1)
                   *   arg.tpe = (Int => Int) { def apply(x$1: Int): Int @loc(Fresh) @pc() }
                   * 
                   * Then, we'd like to find the symbol of the `apply` method in the refinement,
                   * since it's effect is more specific.
                   * 
                   * This is done by searching for all symbols with the right name and then filtering
                   * the one that overrides `pcfun`. However, if there's no overriding (more specific)
                   * symbol, we might actually find `pcfun` itself!
                   */

                  val funSym = arg.tpe.member(pcfun.name).suchThat(m => m.overriddenSymbol(pcfun.owner) == pcfun || m == pcfun)
                  assert(funSym != NoSymbol, "error finding pc function for "+ pcfun +" in "+ arg)
                  
                  val (seenFuns, pcEff) = computePCEffect(funSym, includedFuns, pcInfo, ctx)
                  includedFuns = seenFuns
                  res = lattice.join(res, pcEff)
              }
            }
          }
      }
      res
   }
  
  def computePCEffect(fun: Symbol, includedFuns: Set[Symbol], pcInfo: PCInfo, ctx: Context): (Set[Symbol], Elem) = {
    if (includedFuns contains fun) {
      (includedFuns, lattice.bottom)
    } else {
      var allFuns = includedFuns + fun
      val latent = lookupLatentEffect(fun)
      var resEff = adaptPcEffect(latent, pcInfo, ctx)
      pcEffect(fun) match {
        case None | Some(AnyPC) =>
          resEff = lattice.join(resEff, anyParamCall(fun, ctx))
            
        case Some(PC(calls)) =>
          for (innerInfo @ PCInfo(param, pcfun, pcargtpss) <- calls) {
            if (isParam(param, ctx.owner.enclMethod)) {
              () // see comment above in `adaptToEffectPolymorphism`
            } else {
              val (seenFuns, pcEff) = computePCEffect(pcfun, allFuns, innerInfo, ctx)
              allFuns = seenFuns
              resEff = lattice.join(resEff, pcEff)
            }
          }
      }
      (allFuns, resEff)
    }
  }
  
  /**
   * @implement This method can be overridden by concrete effect checkers. It is
   * intended to define parameter calls of functions defined in external libraries,
   * e.g. the constructor of the class Object, or methods in value classes.
   */
  def pcEffect(fun: Symbol): Option[PCElem] = {
    val annots = fun.tpe.finalResultType.annotations
    val fromAnnot = pcFromAnnotations(annots)
    fromAnnot.orElse(lookupExternalPC(fun))
  }
  
  /**
   * @implement This method can be overridden by concrete effect checkers. It allows to adapt /
   * change / customize effects that have been collected through `@pc` annotations.
   * 
   * By default, returns `eff` unmodified.
   */
  def adaptPcEffect(eff: Elem, pc: PCInfo, ctx: Context): Elem = {
    eff
  }
  

  // @TODO: effect of calling all methods on all types of `args`
  def anyParamCall(args: List[Tree], ctx: Context): Elem =
    (lattice.bottom /: args)((res, arg) => {
      arg match {
        case id @ Ident(_) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
          res
        case _ =>
          lattice.top
      }
    })
    
  def anyParamCall(fun: Symbol, ctx: Context): Elem =
    (lattice.bottom /: fun.tpe.paramss.flatten) {
      case (res, param) => lattice.top
    }
}

*/
