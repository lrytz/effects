package scala.tools.nsc.effects
package xio

import scala.tools.nsc._

class XioChecker(val global: Global) extends EffectChecker[XioLattice] {
  import global._

  val runsAfter = List("xioInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "xioChecker"


  val lattice = new XioLattice
  import lattice.Elem


  // encoding as annotations

  val xioClass   = definitions.getClass("scala.annotation.effects.xio.xio")
  val noXioClass = definitions.getClass("scala.annotation.effects.xio.noXio")

  val annotationClasses = List(xioClass, noXioClass)

  def fromAnnotation(annots: List[AnnotationInfo]) = {
    val xioAnnot = annots.filter(_.atp.typeSymbol == xioClass).headOption
    xioAnnot.map(_ => Xio) orElse {
      val noXioAnnot = annots.filter(_.atp.typeSymbol == noXioClass).headOption
      noXioAnnot.map(_ => NoXio) orElse {
        val pureAnnot = annots.filter(_.atp.typeSymbol == pureAnnotation).headOption
        pureAnnot.map(_ => NoXio)
      }
    }
  }

  def toAnnotation(elem: Elem) = elem match {
    case Xio =>   List(AnnotationInfo(xioClass.tpe, Nil, Nil))
    case NoXio => List(AnnotationInfo(noXioClass.tpe, Nil, Nil))
  }

}