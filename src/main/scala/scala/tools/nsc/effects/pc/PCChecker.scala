package scala.tools.nsc.effects
package pc

import scala.tools.nsc._

class PCChecker(val global: Global) extends EffectChecker[PCLattice] /* with PCCommons[PCLattice] */ {
  import global._
  import analyzer.{Context, Typer}

  val runsAfter = List("pcInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "pcChecker"

  val lattice: pcLattice.type = pcLattice
  import lattice.{PC, AnyPC, PCInfo, ThisLoc, ParamLoc, sameParam, Elem, toElemOps}
  
  val annotationClasses = List(pcClass, anyPcClass)

  val percent = definitions.getMember(definitions.getRequiredModule("scala.annotation.effects.pc"), newTermName("%").encode)
  
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem] = 
    pcFromAnnotation(annots)

  def toAnnotation(elem: Elem): List[AnnotationInfo] = elem match {
    case AnyPC =>
      List(AnnotationInfo(anyPcClass.tpe, Nil, Nil))
    case PC(xs) if !xs.isEmpty =>
      val args = xs map(c => {
        val par = c.param match {
          case ThisLoc(c) => This(c)
          case ParamLoc(p) => Ident(p)
        }
        c.fun match {
          case None =>
            par
          case Some(f) =>
            f.paramss.foldLeft[Tree](Select(par, f))(
              // (fun, params) => Apply(fun, params map (p => Typed(Ident(percent), TypeTree(p.tpe))))
              (fun, params) => Apply(fun, params map (_ => Ident(percent)))
            )
        }
      })
      // every tree needs a type for pickling. types should be correct, else later
      // phases might crash (refchecks). so let's run a typer.
      val typedArgs = args map (typer.typed(_))
      List(AnnotationInfo(pcClass.tpe, typedArgs, List()))
    case _ =>
      Nil // we don't need an annotation if there are no pc calls.
  }
  
  override def nonAnnotatedEffect(method: Option[Symbol]): Elem = lattice.bottom

  override def checkDefDef(dd: DefDef, ddTyper: Typer, unit: CompilationUnit): DefDef = dd
  override def checkValDef(vd: ValDef, vdTyper: Typer, unit: CompilationUnit): ValDef = vd
  
  override def computeApplicationEffect(fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) = {
    var res: Elem = lattice.bottom
    val funSym = fun.symbol

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
    fromAnnotation(funSym.tpe).getOrElse(lattice.bottom) match {
      case AnyPC => ()
      case PC(calls) =>
        for (pcInfo @ PCInfo(param, pcfun) <- calls) {
          if (isParamCall(pcInfo, ctx)) {
            // 1. the annotated param call is still a param call in the current method
            res = res u PC(PCInfo(param, pcfun))
          } else {
            
            val paramTree = param match {
              case ThisLoc(c) =>
                val Select(qual, _) = fun
                qual
                
              case ParamLoc(p) =>
                var j = -1
                val i = funSym.paramss.indexWhere(l => {
                  j = l.indexWhere(sameParam(_, p))
                  j >= 0
                })
                if (i >= 0) {
                  assert(argss.isDefinedAt(i) && argss(i).isDefinedAt(j), "strange arguments when calling "+ pcfun + " on "+ param +": "+ argss)
                  argss(i)(j)
                }
            }
            paramTree match {
              case id @ Ident(_) =>
                val pcInfo = PCInfo(ParamLoc(id.symbol), pcfun)
                if (isParamCall(pcInfo, ctx))
                  res = res u PC(pcInfo)
              case th @ This(_) =>
                val pcInfo = PCInfo(ThisLoc(th.symbol), pcfun)
                if (isParamCall(pcInfo, ctx))
                  res = res u  PC(pcInfo)
              case _ => ()
            }
          }
        }
    }

    /**
     * 3. Check if it is a ParamCall
     */
    fun match {
      case Select(id @ Ident(_), _) =>
        val pcInfo = PCInfo(ParamLoc(id.symbol), Some(funSym))
        if (isParamCall(pcInfo, ctx))
          res = res u PC(pcInfo)

      case Select(th @ This(_), _) =>
        val pcInfo = PCInfo(ThisLoc(th.symbol), Some(funSym))
        if (isParamCall(pcInfo, ctx))
          res = res u PC(pcInfo)
      case _ =>
        ()
    }
    (res, Nil)
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