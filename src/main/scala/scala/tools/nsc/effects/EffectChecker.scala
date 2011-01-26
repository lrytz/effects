package scala.tools.nsc.effects

import scala.tools.nsc._
import scala.tools.nsc.plugins.PluginComponent
import collection.{mutable => m}

abstract class EffectChecker[L <: CompleteLattice] extends PluginComponent {
  // abstract val global: Global
  import global._

  // abstract runsAfter: List[String]
  // abstract phaseName: String

  val lattice: L
  type Elem = lattice.Elem


  /**
   * Wee need to know which annotations denotes the effect of this system.
   * The inference algorithm needs to be able to remove intermediate
   * effect annotations, so it just removes annotations that have a type
   * symbol found in this list.
   */
  val annotationClasses: List[Symbol]

  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem]
  def fromAnnotation(tpe: Type): Option[Elem] = fromAnnotation(tpe.annotations)

  def toAnnotation(elem: Elem): AnnotationInfo


  /**
   *  Add an AnnotationChecker to propagate annotations on types
   */
  global.addAnnotationChecker(new AnnotationChecker {
    override val inferenceOnly = true

    def annotationsConform(tpe1: Type, tpe2: Type) = {
      val eff1 = fromAnnotation(tpe1.annotations).getOrElse(lattice.top)
      val eff2 = fromAnnotation(tpe2.annotations).getOrElse(lattice.top)
      lattice.lte(eff1, eff2)
    }

    // effect annotations are only on return types of refinements. if a lub is computed,
    // then things are handled by `annotationsSpecializeSym`.
    override def annotationsLub(tp: Type, ts: List[Type]) = tp
    /* {
      val effects = ts.map(t => fromAnnotation(t.annotations)).map(_.getOrElse(lattice.bottom))
      val eff = lattice.join(effects: _*)
      tp.withAnnotation(toAnnotation(eff))
    } */

    // see comment on lub
    override def annotationsGlb(tp: Type, ts: List[Type]) = tp
  })


  /**
   *  The EffectChecker phase traverses the tree and checks effect
   * conformance
   */
  def newPhase(prev: Phase): Phase = new StdPhase(prev) {
    def apply(unit: CompilationUnit) {
      EffectChecker.this.unit = unit
      checker(unit.body)
      EffectChecker.this.unit = null
    }
  }

  /**
   * Useful for error reporting
   */
  var unit: CompilationUnit = null



  /**
   * Checks effect conformance
   *  - Method's effect conforms to effect annotation on return type
   *  - Conformance of refinement types with effect annotations
   */
  protected val checker = new Traverser {
    override def traverse(tree: Tree) {
      tree match {
        case dd @ DefDef(_, _, _, _, _, _) =>
          () // jaja

        case Assign(lhs, rhs) =>
          () // check if function type

        case Apply(fun, args) =>
          () // check if function type

        case ValDef(_, _, _, _) =>
          () // check if function type

        case Typed(_, _) =>
          () // check if function type

        case _ =>
          ()
      }
      super.traverse(tree)
    }
  }







  val inferAnnotation: Symbol = definitions.getClass("scala.annotation.effects.infer")
  val pureAnnotation: Symbol = definitions.getClass("scala.annotation.effects.pure")

  // @TODO: when to clear the hashmaps

  /**
   * Contains method symbols for which the latent effect has to
   * be inferrred. These are
   *  - local methods
   *  - private methods
   *  - final methods
   *  - methods annotated with @infer
   *
   */
  val inferEffect: m.Map[Symbol, DefDef] = new m.HashMap()


  /**
   * Contains symbols whose type might be refined with effect
   * annotations in a refinement.
   *
   * For example, in
   *   val a = (x: Int) => throw E
   * the type of `a` changes from `Int => Nothing` to
   * `Int => Nothing { def apply(x: Int) => Nothing @throws[E] }`
   *
   * Another example: In
   *   trait C { def foo(): Int }
   *   val x = new C { def foo() = 1 }
   * the type of `x` changes from `C` to `C { def foo(): Int @pure }`
   */
  val refineType: m.Map[Symbol, DefTree] = new m.HashMap()


  def setEffect(method: Symbol, effect: Elem) {
    def addAnnot(tp: Type): Type = tp match {
      case MethodType(args, res) => copyMethodType(tp, args, addAnnot(res))
      case PolyType(targs, res) => PolyType(targs, addAnnot(res))
      case tp => tp.withAnnotation(toAnnotation(effect))
    }
    method.updateInfo(addAnnot(method.tpe))
  }

}
