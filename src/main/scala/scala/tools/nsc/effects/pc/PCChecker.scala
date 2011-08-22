package scala.tools.nsc.effects
package pc

import scala.tools.nsc._

class PCChecker(val global: Global) extends EffectChecker[PCLattice] /* with PCCommons[PCLattice] */ {
  import global._
  import analyzer.Context

  val runsAfter = List("pcInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "pcChecker"

  val pcCommons = new PCCommons {
    val global: PCChecker.this.global.type = PCChecker.this.global
  }
  import pcCommons._
  
  val lattice: pcLattice.type = pcLattice
  import lattice.{PC, PCInfo, AnyPC, sameParam}
  
  val annotationClasses = List(pcClass, anyPcClass)

  val percent = definitions.getMember(definitions.getModule("scala.annotation.effects.pc"), "%".encode) 
  
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem] = 
    pcFromAnnotations(annots)

  def toAnnotation(elem: Elem): List[AnnotationInfo] = elem match {
    case AnyPC =>
      List(AnnotationInfo(anyPcClass.tpe, Nil, Nil))
    case PC(xs) =>
      val args = xs map(c => {
        c.argtpss.foldLeft[Tree](Select(Ident(c.param), c.fun))(
          (fun, args) => Apply(fun, args map (a => Typed(Ident(percent), TypeTree(a))))
        )
      })
      // every tree needs a type for pickling. types should be correct, else later
      // phases might crash (refchecks). so let's run a typer.
      val typedArgs = args map (typer.typed(_))
      List(AnnotationInfo(pcClass.tpe, typedArgs, List()))
  }
  
  override def latentEffect(fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) = {
    var res: Elem = lattice.bottom
    val currentMethod = ctx.owner.enclMethod

    /** 1. For nested functions, the ParamCalls of the callee might be
     *     also ParamCalls of the caller. Example: both f and g have `x.trim`
     *       def f(x: String) { def g = x.trim; g }
     *
     *  2. If a parameter is forwarded as argument to another function,
     *     we can convert the ParamCall. Example:
     *       def f(x: String) = x.trim  // ParamCall `x.trim`
     *       def g(y: String) = f(y)    // ParamCall `y.trim`
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
        for (PCInfo(param, member, argtpss) <- calls) {
          if (isParam(param, currentMethod)) {
            // 1. the param in @pc is still a param in the current method
            res = lattice.join(res, PCInfo(param, member, argtpss))
          } else {
            // 2. the param in @pc is not a param in the current method, therefore
            //    it has to be a param of the called function.
            var j = -1
            val i = fun.symbol.paramss.indexWhere(l => {
              j = l.indexWhere(sameParam(_, param))
              j >= 0
            })
            assert(argss.isDefinedAt(i) && argss(i).isDefinedAt(j), "pc on non-param: "+ member + " on "+ param +" while calling "+ fun)
            argss(i)(j) match {
              case id @ Ident(_) if (isParam(id.symbol, currentMethod)) =>
                res = lattice.join(res, PCInfo(id.symbol, member, argtpss))
              case _ => ()
            }
          }
        }
    }

    /**
     * 3. Check if it is a ParamCall (the receiver is a parameter)
     */
    fun match {
      case Select(id @ Ident(_), _) =>
        if (isParam(id.symbol, currentMethod))
          // @TODO: this argss thing is too ad-hoc. either kick it out, or add targs as well,
          // and make things work correctly. see comment on PCInfo.
          res = lattice.join(res, PCInfo(id.symbol, fun.symbol, argss map (_.map(_.tpe))))

      case _ =>
        ()
    }
    res
  }

}