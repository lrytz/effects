package scala.tools.nsc.effects

import scala.tools.nsc._
import scala.tools.nsc.plugins.PluginComponent

abstract class EffectInferencer[L <: CompleteLattice] extends PluginComponent {

  val checker: EffectChecker[L]
  protected type Elem = checker.Elem

  val global: checker.global.type = checker.global
  import checker.global._

  def newPhase(prev: Phase): Phase = new StdPhase(prev) {
    def apply(unit: CompilationUnit) {
      traverseDefs(unit.body)
    }
  }

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
    inferType && (
      !sym.owner.isClass ||
      sym.isPrivate
//      sym.isFinal
    ) ||
    sym.tpe.finalResultType.hasAnnotation(checker.refineAnnotation)
  }


  /**
   * Collect:
   *  - DefDef when the result type does not have an effect annotation
   *  - ValDef and DefDef, because the type might become a refinement
   * See comm`ents in the EffectChecker.
   */
  val traverseDefs = new Traverser {
    override def traverse(tree: Tree) {
      tree match {
        case dd @ DefDef(_, _, _, _, tt @ TypeTree(), rhs) =>
          val sym = dd.symbol
          val tp = sym.tpe
          if (checker.fromAnnotation(tp.finalResultType).isEmpty) {
            if (inferEffect(sym)) checker.inferEffect(sym) = dd
            else checker.updateEffect(sym, checker.lattice.top)
          }

          // @TODO: is `wasEmpty` always correct, i.e. does it mean `type was inferred`?
          if (!rhs.isEmpty && inferRefinement(sym, tt.wasEmpty))
            checker.refineType(sym) = dd

        case vd @ ValDef(_, _, tt @ TypeTree(), rhs) if !rhs.isEmpty =>
          val sym = vd.symbol
          if (inferRefinement(sym, tt.wasEmpty))
            checker.refineType(sym) = vd

        case _ => ()
      }
      super.traverse(tree)
    }
  }
}
