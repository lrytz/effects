package scala.tools.nsc.effects
package pc

trait PCTools[L <: CompleteLattice] { this: EffectChecker[L] =>
  import global._
  import analyzer.Context
  
  lazy val pcLattice = new PCLattice {
    val global: PCTools.this.global.type = PCTools.this.global
  }

  import pcLattice.{PC, PCInfo, AnyPC, Elem => PCElem, sameParam}

  /**
   * Convert from annotations to PCElems
   */
  
  private def pcFromAnnot(ann: AnnotationInfo): PCElem = {
    var par: Symbol = NoSymbol
    var fun: Symbol = NoSymbol
    def argtpss(tree: Tree): List[List[Type]] = tree match {
      case TypeApply(fun, targs) =>
        argtpss(fun)
      case Apply(fun, args) =>
        (args map (_.tpe)) :: argtpss(fun)
      case f @ Select(p @ Ident(_), _) =>
        par = p.symbol
        fun = f.symbol
        Nil
      case _ =>
        abort("unexpected tree in pc annotation: "+ tree)
    }
    PC(ann.args.map(arg => {
      val tpss = argtpss(arg).reverse
      PCInfo(par, fun, tpss)
    }))
  }
  
  
  // @TODO: if there's no pc annotation, in means there's no PC call, so we should return PC()
  
  def pcFromAnnotation(annots: List[AnnotationInfo]): Option[PCElem] = {
    val anyPcAnnot = annots.filter(_.atp.typeSymbol == anyPcClass).headOption
    anyPcAnnot.map(_ => AnyPC) orElse {
      val pcAnnots = annots.filter(_.atp.typeSymbol == pcClass)
      if (pcAnnots.isEmpty) {
        val pureAnnotation = definitions.getClass("scala.annotation.effects.pure")
        val pureAnnot = annots.filter(_.atp.typeSymbol == pureAnnotation).headOption
        pureAnnot.map(_ => pcLattice.bottom)
      } else {
        Some(pcLattice.join(pcAnnots.map(pcFromAnnot): _*))
      }
    }
  }
  
  def pcFromAnnotation(tpe: Type): Option[PCElem] = pcFromAnnotation(tpe.finalResultType.annotations)

  

  /*
   * Helper functions
   */
  
  /**
   * @TODO: what about params of Function trees?!?
   */
  def isParam(param: Symbol, currentMethod: Symbol): Boolean = {
    if (currentMethod == NoSymbol) false
    else if (!currentMethod.isMethod) isParam(param, currentMethod.owner)
    else {
      // without atPhase there can be CyclicReferences
      val paramss = atPhase(currentRun.typerPhase)(currentMethod.paramss)
      // "sameParam" compares name and owner (why: see its doc).
      paramss.exists(_.exists(sameParam(_, param))) || isParam(param, currentMethod.owner)
    }
  }
  
  lazy val pcClass = definitions.getClass("scala.annotation.effects.pc.pc")
  lazy val anyPcClass = definitions.getClass("scala.annotation.effects.pc.anyPc")

  
  // @TODO (this is just a stub)
  def isAnnotatedPc(fun: Tree, ctx: Context) = fun match {
    case Select(id @ Ident(_), _) =>
      val currentMethod = ctx.owner.enclMethod
      (isParam(id.symbol, currentMethod)) && false
      
    case _ => false
  }

}