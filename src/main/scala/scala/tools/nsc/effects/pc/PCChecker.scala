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
  import lattice.{PC, PCInfo, AnyPC}
  
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
  
  override def applicationEffect(fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) = {
    var acc: Elem = lattice.bottom
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
     *  @TODO: param calls on final members not necessary; the effect can be computed immediately
     */

    fromAnnotation(fun.symbol.tpe).getOrElse(lattice.bottom) match {
      case AnyPC => ()
      case PC(calls) =>
        for (PCInfo(param, member, argtpss) <- calls) {
          // 1.
          if (isParam(param, currentMethod))
            acc = lattice.join(acc, PCInfo(param, member, argtpss))

            // 2.
            var j = -1
            val i = fun.symbol.paramss.indexWhere(l => {
              j = l.indexOf(param)
              j >= 0
            })
            // The parameter of a ParamCall effect can belong to an outer function!
            if (argss.isDefinedAt(i) && argss(i).isDefinedAt(j))
              argss(i)(j) match {
                case id @ Ident(_) if (isParam(id.symbol, currentMethod)) =>
                  acc = lattice.join(acc, PCInfo(id.symbol, member, argtpss))
                case _ => ()
            }
        }
    }

    /**
     * 3. Check if it is a ParamCall (the receiver is a parameter)
     */
    fun match {
      case Select(id @ Ident(_), _) =>
        if (isParam(id.symbol, currentMethod))
          acc = lattice.join(acc, PCInfo(id.symbol, fun.symbol, argss map (_.map(_.tpe))))

      case _ =>
        ()
    }
    acc
  }

}