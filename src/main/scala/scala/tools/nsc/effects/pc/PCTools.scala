package scala.tools.nsc.effects
package pc

trait PCTools[L <: CompleteLattice] { this: EffectChecker[L] =>
  import global._
  import analyzer.Context
  
  lazy val pcLattice = new PCLattice {
    val global: PCTools.this.global.type = PCTools.this.global
  }

  import pcLattice.{PC, AnyPC, PCInfo, PCLoc, ParamLoc, ThisLoc, PCElem/*, sameParam*/}

  lazy val pcPhase = currentRun.phaseNamed("pcChecker")
  
  /**
   * Convert a @pc annotation to a PCElem
   */
  private def fromPcAnnot(ann: AnnotationInfo): PCElem = {
    def paramFun(tree: Tree): (PCLoc, Option[Symbol]) = tree match {
      case TypeApply(fun, targs) =>
        paramFun(fun)
      case Apply(fun, args) =>
        paramFun(fun)
      case f @ Select(p @ Ident(_), _) =>
        (ParamLoc(p.symbol), Some(f.symbol))
      case f @ Select(t @ This(_), _) =>
        (ThisLoc(t.symbol), Some(f.symbol))
      case p @ Ident(_) =>
        (ParamLoc(p.symbol), None)
      case t @ This(_) =>
        (ThisLoc(t.symbol), None)
      case _ =>
        abort("unexpected tree in pc annotation: "+ tree)
    }
    PC(ann.args.map(arg => {
      val (param, fun) = paramFun(arg)
      PCInfo(param, fun)
    }))
  }
  
  def pcFromAnnotation(annots: List[AnnotationInfo]): Option[PCElem] = {
    val anyPcAnnot = annots.filter(_.atp.typeSymbol == anyPcClass).headOption
    anyPcAnnot.map(_ => AnyPC) orElse {
      val pcAnnots = annots.filter(_.atp.typeSymbol == pcClass)
      if (pcAnnots.isEmpty) {
        None
      } else {
        Some(pcLattice.join(pcAnnots.map(fromPcAnnot): _*))
      }
    }
  }
  
  def pcFromAnnotation(tpe: Type): Option[PCElem] = pcFromAnnotation(tpe.finalResultType.annotations)


  /*
   * Helper functions
   */
  
  lazy val pcClass = definitions.getRequiredClass("scala.annotation.effects.pc.pc")
  lazy val anyPcClass = definitions.getRequiredClass("scala.annotation.effects.pc.anyPc")


  /**
   * Is the function tree `fun` a parameter call in the current context?
   * 
   * If `fun` has the shape of a parameter call, we only need to look at
   * the `@pc` annotations of the current enclosing method, if there is
   * one that covers the call.
   * 
   * We don't have to look at `@pc` annotations of enclosing methods,
   * because the `PCChecker` effect system adds those annotations to inner
   * methods. For example, in
   * 
   *   def f(a: A): B @pc(a.m()) = {
   *     def g() {
   *       a.m()
   *     }
   *   }
   * 
   * the `PCChecer` will add the annotation `@pc(a.m())` to the method `g`.
   */
  def isParamCall(fun: Tree, ctx: Context): Boolean = fun match {
    case Select(id @ Ident(_), _) =>
      val paramCall = PCInfo(ParamLoc(id.symbol), Some(fun.symbol))
      isParamCall(paramCall, ctx)
      
    case Select(th @ This(_), _) =>
      val paramCall = PCInfo(ThisLoc(th.symbol), Some(fun.symbol))
      isParamCall(paramCall, ctx)

    case _ => false
  }

  def isParamCall(paramCall: PCInfo, ctx: Context): Boolean = {
    val currentMethod = ctx.owner.enclMethod
    val tp = atPhase(pcPhase)(currentMethod.tpe)
    pcFromAnnotation(tp).orElse(lookupExternalPC(currentMethod)) match {
      case None => false
      case Some(AnyPC) => true
      case Some(PC(pcs)) =>
        pcs.exists(pc => {
          pcLattice.lteInfo(paramCall, pc)
        })
    }
  }
  
  def hasAnyPCAnnotation(ctx: Context): Boolean = {
    val currentMethod = ctx.owner.enclMethod
    val tp = atPhase(pcPhase)(currentMethod.tpe)
    pcFromAnnotation(tp).orElse(lookupExternalPC(currentMethod)) match {
      case Some(AnyPC) => true
      case _ => false
    }
  }
}