package scala.tools.nsc.effects
package pc

import scala.tools.nsc._

class PCChecker(val global: Global) extends EffectChecker[PCLattice] /* with PCCommons[PCLattice] */ {
  import global._
  import analyzer.Context

  val runsAfter = List("pcInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "pcChecker"

/* @DELETE  val pcCommons = new PCCommons {
    val global: PCChecker.this.global.type = PCChecker.this.global
  }
  import pcCommons._ */

  val lattice: pcLattice.type = pcLattice
  import lattice.{PC, PCInfo, AnyPC, sameParam, Elem}
  
  val annotationClasses = List(pcClass, anyPcClass)

  val percent = definitions.getMember(definitions.getModule("scala.annotation.effects.pc"), "%".encode) 
  
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem] = 
    pcFromAnnotation(annots)

  def toAnnotation(elem: Elem): List[AnnotationInfo] = elem match {
    case AnyPC =>
      List(AnnotationInfo(anyPcClass.tpe, Nil, Nil))
    case PC(xs) if !xs.isEmpty =>
      val args = xs map(c => c.fun match {
        case None =>
          Ident(c.param)
        case Some(f) =>
          f.paramss.foldLeft[Tree](Select(Ident(c.param), f))(
            // (fun, params) => Apply(fun, params map (p => Typed(Ident(percent), TypeTree(p.tpe))))
            (fun, params) => Apply(fun, params map (_ => Ident(percent)))
          )
      })
      // every tree needs a type for pickling. types should be correct, else later
      // phases might crash (refchecks). so let's run a typer.
      val typedArgs = args map (typer.typed(_))
      List(AnnotationInfo(pcClass.tpe, typedArgs, List()))
    case _ =>
      Nil // we don't need an annotation if there are no pc calls.
  }
  
  override def computeApplicationEffect(fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) = {
    var res: Elem = lattice.bottom
    val currentMethod = ctx.owner.enclMethod

    /** 1. For nested functions, the ParamCalls of the callee might be
     *     also ParamCalls of the caller. Example: both f and g have `x.m()`
     *       def f(x: A): R @pc(x.m()) { def g = x.m(); g }
     *
     *  2. If a parameter is forwarded as argument to another function,
     *     we can convert the ParamCall. Example:
     *       def f(a1: A) = a1.m()  // @pc(a1.m())
     *       def g(a2: A) = f(a2)   // @pc(a2.m())
     *
     * When there's no @pc annotation on the called function, we use lattice.bottom,
     * i.e. @pc(). There are no @pc effects that can be translated to the current
     * method as described above.
     * 
     * Similarly, when the called function has an @anyPc effect, we don't translate
     * or copy it to the current method.
     * 
     * Instead, each concrete effect system will again look at the pc effect of the
     * called function, and if it's AnyPC, or there's no annotation, it will include
     * the effect of calling every method on every argument.
     */
    fromAnnotation(fun.symbol.tpe).getOrElse(lattice.bottom) match {
      case AnyPC => ()
      case PC(calls) =>
        for (pcInfo @ PCInfo(param, pcfun) <- calls) {
          if (isParamCall(pcInfo, ctx)) {
            // 1. the annotated param call is still a param call in the current method
            res = lattice.join(res, PC(PCInfo(param, pcfun)))
          } else {
            var j = -1
            val i = fun.symbol.paramss.indexWhere(l => {
              j = l.indexWhere(sameParam(_, param))
              j >= 0
            })
            if (i >= 0) {
              assert(argss.isDefinedAt(i) && argss(i).isDefinedAt(j), "strange arguments when calling "+ pcfun + " on "+ param +": "+ argss)
              argss(i)(j) match {
                case id @ Ident(_) if isParamCall(PCInfo(id.symbol, pcfun), ctx) =>
                  res = lattice.join(res, PC(PCInfo(id.symbol, pcfun)))
                case th @ This(_) if isParamCall(PCInfo(th.symbol, pcfun), ctx) =>
                  res = lattice.join(res, PC(PCInfo(th.symbol, pcfun)))
                case _ => ()
              }
            }
          }
        }
    }

    /**
     * 3. Check if it is a ParamCall (the receiver is a parameter)
     */
    fun match {
      case Select(id @ Ident(_), _) =>
        if (isParamCall(PCInfo(id.symbol, Some(currentMethod)), ctx))
          res = lattice.join(res, PC(PCInfo(id.symbol, Some(fun.symbol))))

      case Select(th @ This(_), _) =>
        if (isParamCall(PCInfo(th.symbol, Some(currentMethod)), ctx))
          res = lattice.join(res, PC(PCInfo(th.symbol, Some(fun.symbol))))
      case _ =>
        ()
    }
    res
  }

  /**
   * Since @pc annotations are not yet propagated to nested methods, we need to look at
   * the entire method owner chain to find out if a given paramCall is annotated as such.
   * 
   * In later effect checking phases, this is not necessary. See documentation of method
   * `isParamCall` in PCTools.
   */
  override def isParamCall(paramCall: PCInfo, ctx: Context): Boolean = {
    def test(meth: Symbol): Boolean = {
      if (meth == NoSymbol) false
      else {
        atPhase(currentRun.typerPhase) {
          pcFromAnnotation(meth.tpe).orElse(lookupExternalPC(meth))
        } match {
          case None => test(meth.enclMethod)
          case Some(AnyPC) => true
          case Some(PC(pcs)) =>
            pcs.exists(pc => {
              pcLattice.lteInfo(paramCall, pc)
            }) || test(meth.enclMethod)
        }
      }
    }
    test(ctx.owner.enclMethod)
  }
}