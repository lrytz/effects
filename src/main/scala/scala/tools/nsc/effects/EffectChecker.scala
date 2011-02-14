package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.TypingTransformers
import plugins.PluginComponent
import collection.{mutable => m}

abstract class EffectChecker[L <: CompleteLattice] extends PluginComponent with TypingTransformers {
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

  /**
   * @TODO: treat `@pure` here, i.e. let every subclass decide how to handle it?
   * or assign `lattice.bottom` directly in the EffectInferencer?
   */
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem]
  def fromAnnotation(tpe: Type): Option[Elem] = fromAnnotation(tpe.finalResultType.annotations)

  def toAnnotation(elem: Elem): AnnotationInfo



  /**
   *  The EffectChecker phase traverses the tree and checks effect
   * conformance
   */
  def newPhase(prev: Phase): Phase = new StdPhase(prev) {
    def apply(unit: CompilationUnit) {
      EffectChecker.this.unit = unit
      checker.transformUnit(unit)
      EffectChecker.this.unit = null
    }
  }



  /**
   * Useful for error reporting
   */
  var unit: CompilationUnit = null

  /**
   * This method is called when the actual effect of a method does not conform
   * to the annotated one.
   */
  def effectError(tree: Tree, expected: Elem, found: Elem) {
    unit.error(tree.pos, "effect error.\nexpected: "+ expected +"\nfound: "+ found)
  }

  /**
   * This method is called when an overriding method has a larger
   * effect than the overridden one.
   */
  def overrideError(tree: Tree, overridden: Symbol, expected: Elem, found: Elem) {
    effectError(tree, expected, found)
  }

  def refinementError(tree: Tree, expected: Type, found: Type) {
    unit.error(tree.pos, "effect type error.\nexpected: "+ expected +"\nfound: "+ found)
  }


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
  })



  /**
   * Checks effect conformance
   *  - Method's effect conforms to effect annotation on return type
   *  - Conformance of refinement types with effect annotations
   */
  protected val checker = new Transformer {
    override def transform(tree: Tree): Tree = {
      tree match {
        case dd @ DefDef(_, _, _, _, _, _) =>
          val td = super.transform(dd)
          checkDefDef(td)

        case vd @ ValDef(_, _, _, _) =>
          val td = super.transform(vd)
          checkValDef(td)

        case _ =>
          super.transform(tree)
      }
    }
  }



  val inferAnnotation: Symbol = definitions.getClass("scala.annotation.effects.infer")
  val refineAnnotation: Symbol = definitions.getClass("scala.annotation.effects.refine")
  val pureAnnotation: Symbol = definitions.getClass("scala.annotation.effects.pure")

  // @TODO: when to clear the hashmaps

  /**
   * Contains method symbols for which the latent effect has to
   * be inferrred. These are
   *  - local methods
   *  - private methods
   *  - final methods (maybe?)
   *  - methods annotated with @infer
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
  val refinedType: m.Set[Symbol] = new m.HashSet()

  /**
   * Caches the result of `computeEffect` on the `rhs` of a DefDef
   * or ValDef. It is used to avoid calling `computeEffect` twice
   * on the same tree. It's used in two fashions:
   *  - to obtain the result of a previous `computeEffect`
   *  - to check if `computeEffect` has already been run before
   *    looking at `rhs.tpe`
   */
  val rhsEffect: m.Map[Symbol, Elem] = new m.HashMap()

  /**
   * Remove from `tp` all annotations whose annotation
   * class symbol is present in the list `cls`.
   */
  def removeAnnotations(tp: Type, cls: List[Symbol]): Type = tp match {
    case AnnotatedType(annots, underlying, _) =>
      underlying.withAnnotations(annots.filterNot(ann => cls.contains(ann.atp.typeSymbol)))
    case tp => tp
  }

  /**
   * Change the result type of `tp` using the function `op`.
   */
  def onResultType(tp: Type, op: Type => Type): Type = tp match {
    case MethodType(args, res)  => copyMethodType(tp, args, onResultType(res, op))
    case PolyType(targs, res)   => PolyType(targs, onResultType(res, op))
    case NullaryMethodType(res) => NullaryMethodType(onResultType(res, op))
    case tp => op(tp)
  }

  /**
   *  Updates the effect annotation on `method` to `annot`.
   */
  def updateEffect(method: Symbol, annot: AnnotationInfo) {
    method.updateInfo(onResultType(method.tpe, rt => {
      removeAnnotations(rt, annotationClasses).withAnnotation(annot)
    }))
  }

  /**
   * Updates the effect annotation on `method` to `effect`.
   */
  def updateEffect(method: Symbol, effect: Elem) {
    updateEffect(method, toAnnotation(effect))
  }

  def maybeInferEffect(method: Symbol) {
    if (inferEffect.contains(method) && fromAnnotation(method.tpe).isEmpty) {
      val rhs = inferEffect(method).rhs
      updateEffect(method, rhsEffect.getOrElseUpdate(method, computeEffect(rhs)))
    }
  }

  /**
   * Returns the latent effect of `method` by applying
   * effect inference before when necessary.
   */
  def effectOf(method: Symbol): Option[Elem] = {
    maybeInferEffect(method)
    fromAnnotation(method.tpe)
  }

  /**
   * Updates the result type of `sym` to `newRt`, but keeps the
   * annotations of the current result type.
   */
  def updateResultType(sym: Symbol, newRt: Type) {
    sym.updateInfo(onResultType(sym.tpe, oldRt => {
      assert(newRt <:< oldRt, "effect-refined type does not conform: "+ newRt +" <:< "+ oldRt)
      removeAnnotations(newRt, annotationClasses).withAnnotations(oldRt.annotations)
    }))
  }

  def maybeInferType(sym: Symbol) {
    // @TODO: un-copy-paste from Namers.scala

    // EVEN BETTER: call "typedValDef" instead of re-doing part of the work

    def widenIfNecessary(sym: Symbol, tpe: Type, pt: Type): Type = {
      val getter =
        if (sym.isValue && sym.owner.isClass && sym.isPrivate)
          sym.getter(sym.owner)
        else sym
      def isHidden(tp: Type): Boolean = tp match {
        case SingleType(pre, sym) =>
          (sym isLessAccessibleThan getter) || isHidden(pre)
        case ThisType(sym) =>
          sym isLessAccessibleThan getter
        case p: SimpleTypeProxy =>
          isHidden(p.underlying)
        case _ =>
          false
      }
      val tpe1 = tpe.deconst
      val tpe2 = tpe1.widen
      if ((sym.isVariable || sym.isMethod && !sym.hasAccessorFlag))
        if (tpe2 <:< pt) tpe2 else tpe1
      else if (isHidden(tpe)) tpe2
      else if (sym.isFinal || sym.isLocal) tpe
      else tpe1
    }

    if (refineType contains sym) {
      val newTpe = {
        val rhs = refineType(sym) match {
          case DefDef(_, _, _, _, _, rhs) => rhs
          case ValDef(_, _, _, rhs) => rhs
        }
        rhsEffect.getOrElseUpdate(sym, computeEffect(rhs))
        typer.packedType(rhs, sym.owner)
      }
      updateResultType(sym, widenIfNecessary(sym, newTpe, typeOf(sym).finalResultType))
      refineType.remove(sym)
      refinedType += sym
    }
  }
  /**
   * Returns the type of `sym` by applying effect type
   * inference before when necessary.
   */
  def typeOf(sym: Symbol): Type = {
    maybeInferType(sym)
    sym.tpe
  }


  /**
   * Check a DefDef tree
   *  - that effect of the body conforms to the annotated effect
   *  - that the type of the body conforms to the annotated type
   *  - that no type or effect is larger than from an overridden method
   */
  def checkDefDef(dd: DefDef): DefDef = {
    val sym = dd.symbol

    // Check or infer the latent effect
    val symEff = effectOf(sym).getOrElse(abort("no latent effect annotation on "+ sym))
    val rhsEffOpt =
      if (inferEffect contains sym) None
      else Some(rhsEffect.getOrElseUpdate(sym, computeEffect(dd.rhs)))

    for (rhsEff <- rhsEffOpt) {
      if (!lattice.lte(rhsEff, symEff))
        effectError(dd, symEff, rhsEff)
    }

    // Check or infer the return type
    if (!sym.isConstructor) {
      val symTp = typeOf(sym).finalResultType
      val rhsTpOpt =
        if (dd.rhs.isEmpty || refinedType(sym)) None
        else {
          rhsEffect.getOrElseUpdate(sym, computeEffect(dd.rhs))
          Some(dd.rhs.tpe)
        }

      for (rhsTp <- rhsTpOpt) {
        // @TODO: what about type parameters and finalResultType???
        //  def f[T](x: T): T = x
        checkRefinement(dd, rhsTp, symTp)
      }

      // check the latent effect and return type for all overridden methods
      for (os <- sym.allOverriddenSymbols) {
        // @TODO: lattice.top when overridden does not have an effect annotation?
        val overriddenEffect = effectOf(os).getOrElse(lattice.top)
        if (!lattice.lte(symEff, overriddenEffect))
          overrideError(dd, os, overriddenEffect, symEff)
        checkRefinement(dd, typeOf(os).finalResultType, symTp)
      }
    }
  }

  def checkValDef(vd: ValDef): ValDef = {
    val sym = vd.symbol

    val symTp = typeOf(sym)
    val rhsTpOpt =
      if (vd.rhs.isEmpty || refinedType(sym)) None
      else {
        rhsEffect.getOrElseUpdate(sym, computeEffect(vd.rhs))
        Some(vd.rhs.tpe)
      }

    for (rhsTp <- rhsTpOpt) {
      checkRefinement(vd, rhsTp, symTp)
    }

    for (os <- sym.allOverriddenSymbols) {
      checkRefinement(vd, typeOf(os), symTp)
    }
  }

  def checkRefinement(tree: Tree, tp1: Type, tp2: Type) {
    // @TODO: should only enable annotation checking for current effects
    // system, not for all
    if (!annotsInferMode(tp1 <:< tp2)) {
      refinementError(tree, tp1, tp2)
    }
  }


  /**
   * Does two things
   *  - compute and return the effect caused by executing `tree`
   *  - update `tree.tpe` to a more precise type (a refinement
   *    containing effect annotations)
   *
   * @TODO: should only allow ValDef or DefDef rhs trees (right?)
   */
  def computeEffect(tree: Tree) =
    newEffectTraverser(tree).compute()

  def newEffectTraverser(tree: Tree): EffectTraverser = new EffectTraverser(tree)

  class EffectTraverser(tree: Tree) extends Traverser {
    override def apply[T <: Tree](t: T): T = abort("apply should not be called")

    def compute(): Elem = {
      acc = lattice.bottom
      traverse(tree)
      acc
    }

    protected var acc: Elem = lattice.bottom
    protected def add(eff: Elem) { acc = lattice.join(acc, eff) }

    protected def retypeTo(stop: Tree) {
      new ResetTraverser(stop).traverse(tree)
      typer.typed(tree)
    }

    override def traverse(tree: Tree) {
      tree match {
        case ClassDef(_, _, _, _) => ()
        case ModuleDef(_, _, _) => ()
        case DefDef(_, _, _, _, _, _) => ()


        case ValDef(_, _, _, rhs) =>
          val sym = tree.symbol
          if (!sym.isLazy) {
            val oldTpe = rhs.tpe
            // possibly infer refinement (if so, rhsEffect is updated)
            typeOf(sym)
            add(rhsEffect.getOrElseUpdate(sym, computeEffect(rhs)))
            if (oldTpe != rhs.tpe)
              retypeTo(tree)
          }

        case Select(qual, name) =>
          val sym = tree.symbol


        // refine the type
        case Function(_, body) => ()

        case _ => ()
      }
    }

    private class ResetTraverser(stop: Tree) extends Traverser {
      private val trace: m.Stack[Tree] = new m.Stack()

      def reset(t: Tree) {
        if (tree.hasSymbol) tree.symbol = NoSymbol
        t match {
          case EmptyTree => // tpe_= throws an exception
            ()
          case tt @ TypeTree() =>
            if (tt.wasEmpty) tt.tpe = null
          case _ =>
            tree.tpe = null
        }
      }

      override def traverse(tree: Tree) {
        if (tree == stop) {
          for (t <- trace)
            reset(t)
        } else {
          trace.push(tree)
          super.traverse(tree)
          trace.pop()
        }
      }
    }
  }
}
