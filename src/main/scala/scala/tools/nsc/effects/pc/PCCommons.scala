package scala.tools.nsc.effects
package pc

import scala.tools.nsc._

abstract class PCCommons {

  val global: Global

  lazy val pcLattice = new PCLattice {
    val global: PCCommons.this.global.type = PCCommons.this.global
  }

  import global._
  import pcLattice.{PC, PCInfo, AnyPC, Elem}

  def isParam(param: Symbol, currentMethod: Symbol): Boolean = {
    if (currentMethod == NoSymbol) false
    else if (!currentMethod.isMethod) isParam(param, currentMethod.owner)
    else {
      // without atPhase there can be CyclicReferences
      val paramss = atPhase(currentRun.typerPhase)(currentMethod.paramss)
      paramss.exists(_.exists(_ == param)) || isParam(param, currentMethod.owner)
      
    }
  }

  lazy val pcClass = definitions.getClass("scala.annotation.effects.pc.pc")
  lazy val anyPcClass = definitions.getClass("scala.annotation.effects.pc.anyPc")

  private def pcFromAnnot(ann: AnnotationInfo): Elem = {
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
  
  def pcFromAnnotations(annots: List[AnnotationInfo]): Option[Elem] = {
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

}