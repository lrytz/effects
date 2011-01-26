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
   * method is not part of an API, then the effect should be inferred.
   */
  def inferEffect(sym: Symbol): Boolean = {
    !sym.owner.isClass ||
    sym.isPrivate ||
    sym.isFinal ||
    sym.tpe.finalResultType.hasAnnotation(checker.inferAnnotation)
  }

  /**
   * When the type (return type for methods) was inferred and the
   * method is not part of an API, or there is the @infer annotation,
   * then the effect should also be inferred.
   *
   * @TODO: infer public final functions? and if so, check for final owner.
   */
  def inferRefinement(sym: Symbol, inferType: Boolean): Boolean = {
    inferType && (
      !sym.owner.isClass ||
      sym.isPrivate ||
      sym.isFinal
    ) ||
    sym.tpe.finalResultType.hasAnnotation(checker.inferAnnotation)
  }


  /**
   * Collect:
   *  - DefDef when the result type does not have an effect annotation
   *  - ValDef and DefDef, because the type might become a refinement
   * See comments in the EffectChecker.
   */
  val traverseDefs = new Traverser {
    override def traverse(tree: Tree) {
      tree match {
        case dd @ DefDef(_, _, _, _, _, _) =>
          val sym = dd.symbol
          val tp = sym.tpe
          if (checker.fromAnnotation(tp.finalResultType).isEmpty) {
            if (inferEffect(sym)) checker.inferEffect(sym) = dd
            else checker.setEffect(sym, checker.lattice.top)
          }

          // @TODO: look at `original` to know about type inference?
          val tt @ TypeTree() = dd.tpt
          if (inferRefinement(sym, tt.original == null))
            checker.refineType(sym) = dd

        case vd @ ValDef(_, _, tt @ TypeTree(), _)=>
          val sym = vd.symbol
          if (inferRefinement(sym, tt.original == null))
            checker.refineType(sym) = vd

        case _ => ()
      }
    }
  }
}
