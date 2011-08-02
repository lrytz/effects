package scala.tools.nsc.effects
package pc

trait PCTracking[L <: CompleteLattice] extends EffectChecker[L] { /* this: EffectChecker[L] => */
  import global._
  import analyzer.Context

  val pcCommons = new PCCommons {
    val global: PCTracking.this.global.type = PCTracking.this.global
  }
  import pcCommons._
  import pcLattice.{PC, PCInfo, AnyPC}

  
  override def adaptToEffectPolymorphism(latent: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    
    /* If the receiver of the function is a parameter then it's a parameter call. Therefore
     * we can ignore the effect, it is represented by the @pc annotation (which is already
     * present from the PCChecker phase). Example:
     * 
     *   def foo(a: A): B @pc(a.bar) = a.bar
     * 
     * The side-effect of the application `a.bar` does not have to be annotated, it's covered
     * by the `@pc(a.bar)` annotation.
     */
    var res = fun match {
      case Select(id @ Ident(_), _) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
        lattice.bottom
      case _ =>
        latent
    }

    val flatArgss = argss.flatten
    val flatParamss = fun.symbol.tpe.paramss.flatten

    val annots = fun.symbol.tpe.finalResultType.annotations
    pcFromAnnotations(annots) match {
      case None | Some(AnyPC) =>
        res = lattice.join(res, anyParamCall(flatArgss, ctx))
      case Some(PC(calls)) =>
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
            val i = flatParamss.indexOf(param)
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
                // @TODO: problem here. arg.tpe is the type during type-checking, but we need the more up-to-date (refined) one. or is it refined? then why does it not work? :P
                val funTpe = arg.tpe.memberType(pcfun)
                val pcEff = fromAnnotation(funTpe).getOrElse(lattice.top)
                res = lattice.join(res, adaptPcEffect(pcEff, pcInfo, fun, targs, argss, ctx))
            }
          }
        }
    }
    res
  }

  /**
   * @implement This method can be overridden by concrete effect checkers. It allows to adapt /
   * change / customize effects that have been collected through `@pc` annotations of the
   * applied function `fun`.
   * 
   * By default, it calls calls the method `adaptLatentEffect` defined in `EffectCheckers`.
   */
  def adaptPcEffect(eff: Elem, pc: PCInfo, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    adaptLatentEffect(eff, fun, targs, argss, ctx)
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
}
