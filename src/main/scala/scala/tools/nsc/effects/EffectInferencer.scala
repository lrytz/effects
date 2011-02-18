package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{Transform, TypingTransformers}
import plugins.PluginComponent

abstract class EffectInferencer[L <: CompleteLattice] extends PluginComponent with Transform with TypingTransformers {

  val checker: EffectChecker[L]
  protected type Elem = checker.Elem

  val global: checker.global.type = checker.global
  import checker.global._

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
   * @TODO: also infer if there's a private or local owner somewhere! e.g.
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
    sym.tpe.finalResultType.hasAnnotation(checker.inferAnnotation)
  }

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
    sym.tpe.finalResultType.typeSymbol != definitions.UnitClass && {
      inferType && (
        !sym.owner.isClass ||
          sym.isPrivate
//      sym.isFinal
        ) ||
        sym.tpe.finalResultType.hasAnnotation(checker.refineAnnotation)
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
      tree match {
        case dd @ DefDef(_, _, _, _, tt @ TypeTree(), rhs) =>
          val sym = dd.symbol
          val tp = sym.tpe

          /**
           * @TODO: VERY PROBLEMATIC for multiple effect systems.
           *
           * When a refinement needs to be inferred in more than one system,
           * the already existing ones must stay!!!
           */

          val hasNoE = checker.fromAnnotation(tp.finalResultType).isEmpty
          val inferE = hasNoE && inferEffect(sym)
          // @TODO: is `wasEmpty` always correct, i.e. does it mean `type was inferred`?
          val inferT = !rhs.isEmpty && inferRefinement(sym, tt.wasEmpty)

          if (inferE)
            checker.inferEffect(sym) = dd
          else if (hasNoE)
            checker.updateEffect(sym, checker.lattice.top)

          if (inferT)
            checker.refineType(sym) = dd

          if (inferE || inferT)
            // @TODO: updateInfo makes assertion crash..
            sym.setInfo(mkLazyType(sym => {
              // @TODO: if !hasNoE, then we need to keep the annotated effect!!!
              val refinedType =
                if (inferT) checker.computeType(sym, tp, typer, currentClass, unit)
                else tp

              val annotType =
                if (inferE) checker.typeWithEffect(tp, checker.computeEffect(sym))
                else tp

              // @TODO: lazy types should probably not remain in TypeHistory...
              sym.updateInfo(annotType)
            }))

        case vd @ ValDef(_, _, tt @ TypeTree(), rhs) if !rhs.isEmpty =>
          val sym = vd.symbol
          val tp = sym.tpe
          if (inferRefinement(sym, tt.wasEmpty)) {
            checker.refineType(sym) = vd
            sym.setInfo(mkLazyType(sym => {
              sym.updateInfo(checker.computeType(sym, tp, typer, currentClass, unit))
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
