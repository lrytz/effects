package scala.tools.nsc.effects
package simple

import pc._
import scala.tools.nsc._

class SimpleChecker(val global: Global) extends EffectChecker[SimpleLattice] with PCTracking[SimpleLattice] {
  import global._

  val runsAfter = List("simpleInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "simpleChecker"


  val lattice = new SimpleLattice


  // encoding as annotations

  val effClass   = definitions.getClass("scala.annotation.effects.simple.eff")
  val noEffClass = definitions.getClass("scala.annotation.effects.simple.noEff")

  val annotationClasses = List(effClass, noEffClass)

  def fromAnnotation(annots: List[AnnotationInfo]) = {
    val pureAnnot = annots.filter(_.atp.typeSymbol == pureAnnotation).headOption
    pureAnnot.map(_ => NoEff) orElse {
      val effAnnot = annots.filter(_.atp.typeSymbol == effClass).headOption
      effAnnot.map(_ => Eff) orElse {
        val noEffAnnot = annots.filter(_.atp.typeSymbol == noEffClass).headOption
        noEffAnnot.map(_ => NoEff)
      }
    }
  }

  def toAnnotation(elem: Elem) = elem match {
    case Eff =>   AnnotationInfo(effClass.tpe, Nil, Nil)
    case NoEff => AnnotationInfo(noEffClass.tpe, Nil, Nil)
  }
}
