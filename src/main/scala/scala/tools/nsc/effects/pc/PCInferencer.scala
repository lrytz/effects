package scala.tools.nsc.effects
package pc

trait PCInferencer extends EffectInferencer[PCLattice] {
  val checker: PCChecker
  
  import checker._
  import global._
  import lattice.Elem

  override def inferEffect(sym: Symbol) = {
    isNestedInAnnotated(sym)
  }

  override def inferConstructorEffect(sym: Symbol) = {
    isNestedInAnnotated(sym)
  }
  
  override def inferRefinement(sym: Symbol, typeWasInferred: Boolean): Boolean = {
    sym.tpe.finalResultType.typeSymbol != definitions.UnitClass &&
    !sym.isConstructor &&
    typeWasInferred &&
    isNestedInAnnotated(sym)
  }

  def isNestedInAnnotated(sym: Symbol): Boolean = {
    if (sym == NoSymbol) false
    else {
      val o = sym.owner
      lazy val annots = if (o.isPrimaryConstructor) {
        o.owner.annotations
      } else if (o.isConstructor) {
        o.annotations
      } else {
        o.tpe.finalResultType.annotations
      }
      (o.isMethod && !fromAnnotation(annots).isEmpty) || isNestedInAnnotated(o)
    }
  }
}