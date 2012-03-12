package scala.tools.nsc.effects
package simple

import pc._
import scala.tools.nsc._

class SimpleChecker(val global: Global) extends EffectChecker[SimpleLattice] {
  import global._

  val runsAfter = List("simpleInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "simpleChecker"


  val lattice = new SimpleLattice
  import lattice.Elem


  // encoding as annotations

  val effClass   = definitions.getRequiredClass("scala.annotation.effects.simple.eff")
  val noEffClass = definitions.getRequiredClass("scala.annotation.effects.simple.noEff")

  val annotationClasses = List(effClass, noEffClass)

  def fromAnnotation(annots: List[AnnotationInfo]) = {
    val effAnnot = annots.filter(_.atp.typeSymbol == effClass).headOption
    effAnnot.map(_ => Eff) orElse {
      val noEffAnnot = annots.filter(_.atp.typeSymbol == noEffClass).headOption
      noEffAnnot.map(_ => NoEff) orElse {
        val pureAnnot = annots.filter(_.atp.typeSymbol == pureAnnotation).headOption
        pureAnnot.map(_ => NoEff)
      }
    }
  }

  def toAnnotation(elem: Elem) = elem match {
    case Eff =>   List(AnnotationInfo(effClass.tpe, Nil, Nil))
    case NoEff => List(AnnotationInfo(noEffClass.tpe, Nil, Nil))
  }
}
