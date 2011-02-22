package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{Transform, TypingTransformers}
import plugins.PluginComponent

abstract class EffectInferencer[L <: CompleteLattice] extends PluginComponent with Transform with TypingTransformers {

  val checker: EffectChecker[L]
  import checker._
//  protected type Elem = checker.Elem

  val global: checker.global.type = checker.global
  import global._

// Not needed, implemented by trait `Transform`
//  def newPhase(prev: Phase): Phase = new StdPhase(prev) {
//    def apply(unit: CompilationUnit) {
//      inferTransformer(unit).transformUnit(unit)
//    }
//  }

  /**
   * When the result type does not have an effect annotation and the
   * method is not part of an API or there is the @infer annotation,
   * then the effect should be inferred.
   *
   * @TODO: infer public final methods? if so, also check for final owner.
   *
   * @TODO: also infer if there's a private or local owner somewhere, or when the class is anonymous! e.g.
   *   val c = {
   *     class anon extends C {
   *       def f(): Int = 1           // should infer effect of f
   *     }
   *     new anon
   *   }
   */
  def inferEffect(sym: Symbol): Boolean = {
    !sym.owner.isClass ||
    sym.isPrivate ||
//    sym.isFinal ||
    sym.tpe.finalResultType.hasAnnotation(inferAnnotation)
  }

  def inferConstructorEffect(sym: Symbol): Boolean = false

  def getterEffect(sym: Symbol): Elem = lattice.bottom
  def setterEffect(sym: Symbol): Elem = lattice.bottom

  /**
   * When the type of a value (return type for methods) was inferred
   * and the definition is not part of an API, or there is the @refine
   * annotation, refinement type with more precise effects should be
   * inferred.
   *
   * @TODO: infer for final?
   */
  def inferRefinement(sym: Symbol, inferType: Boolean): Boolean = {
    // Unit is never refined
    sym.tpe.finalResultType.typeSymbol != definitions.UnitClass &&
    !sym.isConstructor && {
      inferType && (
        !sym.owner.isClass ||
          sym.isPrivate
//      sym.isFinal
        ) ||
        sym.tpe.finalResultType.hasAnnotation(refineAnnotation)
    }
  }


  /**
   * Collect:
   *  - DefDef when the result type does not have an effect annotation
   *  - ValDef and DefDef, because the type might become a refinement
   * See comm`ents in the EffectChecker.
   */
  def newTransformer(unit: CompilationUnit) = new TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      val sym = tree.symbol

      // `currentClass` and `localTyper` are both variables in the TypingTransformer,
      // so when a closure references them via $outer, it will see the values at the
      // time it's executed, not the current values.
      val transOwner = currentOwner
      val transTyper = localTyper
      tree match {
          /*
        case DefDef(_, _, _, _, _, _) if sym.isGetter =>
          updateEffect(sym, getterEffect(sym))

        case DefDef(_, _, _, _, _, _) if sym.isSetter =>
          updateEffect(sym, setterEffect(sym))
*/
        case DefDef(_, _, _, _, _, _) if (sym.isGetter || sym.isSetter) =>
          ()

        case dd @ DefDef(_, _, _, _, tt @ TypeTree(), rhs) =>

          /**
           * @TODO: VERY PROBLEMATIC for multiple effect systems.
           *
           * When a refinement needs to be inferred in more than one system,
           * the already existing ones must stay!!!
           */

          // If "tt" was inferred, then there might be a wrong effect annotation. Example:
          //   class C { def f: Int @noEff }
          //   def m = getC().f
          // Typer infers type `Int @noEff` for m, which is wrong.

          // @TODO: does this work with multiple systems???

          val hasNoE = tt.wasEmpty || fromAnnotation(sym.tpe).isEmpty
          val inferE = hasNoE && inferEffect(sym) && (!sym.isConstructor || inferConstructorEffect(sym))
          // @TODO: is `wasEmpty` always correct, i.e. does it mean `type was inferred`?
          val inferT = !rhs.isEmpty && inferRefinement(sym, tt.wasEmpty)

          if (inferE)
            checker.inferEffect(sym) = dd
          else if (hasNoE)
            updateEffect(sym, lattice.top)

          if (inferT)
            refineType(sym) = dd

          val tp = sym.tpe // updateEffect called above changes this type (adds an effect)!
          if (inferE || inferT)
            // @TODO: updateInfo to lazy type is not allowed. Is setInfo OK?
            sym.setInfo(mkLazyType(sym => {
              val refinedType =
                if (inferT) computeType(sym, tp, transTyper, transOwner, unit)
                else tp

              val annotType =
                if (inferE) typeWithEffect(refinedType, computeEffect(sym))
                else refinedType

              // @TODO: lazy types should probably not remain in TypeHistory...
              sym.updateInfo(annotType)
            }))

        case vd @ ValDef(_, _, tt @ TypeTree(), rhs) =>
          if (rhs.isEmpty || !inferRefinement(sym, tt.wasEmpty)) {
            val getter = sym.getter(sym.owner)
            if (getter != NoSymbol)
              updateEffect(getter, getterEffect(getter))
            val setter = sym.setter(sym.owner)
            if (setter != NoSymbol)
              updateEffect(setter, setterEffect(setter))
          } else {
            val tp = sym.tpe
            refineType(sym) = vd

            sym.setInfo(mkLazyType(_ => {
              sym.updateInfo(computeType(sym, tp, transTyper, transOwner, unit))
            }))

            val getter = sym.getter(sym.owner)
            if (getter != NoSymbol)
              getter.setInfo(mkLazyType(_ => {
                val refinedType = computeType(sym, tp, transTyper, transOwner, unit)
                val getterType = typeWithEffect(NullaryMethodType(refinedType), getterEffect(getter))
                getter.updateInfo(getterType)
              }))

            val setter = sym.setter(sym.owner)
            if (setter != NoSymbol)
              setter.setInfo(mkLazyType(_ => {
                val arg = setter.newSyntheticValueParam(computeType(sym, tp, transTyper, transOwner, unit))
                val setterType = typeWithEffect(MethodType(List(arg), definitions.UnitClass.tpe), setterEffect(setter))
                setter.updateInfo(setterType)
              }))
          }

        case DefDef(_, _, _, _, _, _) => abort("Unexpected DefDef: no tpt @ TypeTree()")
        case ValDef(_, _, _, _)       => abort("Unexpected ValDef: no tpt @ TypeTree()")
        case _ => ()
      }

      super.transform(tree)
    }
  }

  def mkLazyType(c: Symbol => Unit) = new LazyType {
    override def complete(s: Symbol) {
      c(s)
    }
  }
}
