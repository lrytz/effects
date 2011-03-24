package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{ Transform, TypingTransformers }
import plugins.PluginComponent
import collection.{ mutable => m }

abstract class EffectChecker[L <: CompleteLattice] extends PluginComponent with Transform with TypingTransformers {
  // abstract val global: Global
  import global._
  import analyzer.{Typer, Context}

  // abstract runsAfter: List[String]
  // abstract phaseName: String

  /**
   * *******
   * STATE
   * ******
   */

  // @TODO: when to clear the hashmaps

  /**
   * Contains method symbols for which the latent effect has to
   * be inferrred. These are
   *  - local methods
   *  - private methods
   *  - final methods (maybe?)
   *  - methods annotated with @infer
   */
  val inferEffect: m.Set[Symbol] = new m.HashSet()

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
  val refineType: m.Set[Symbol] = new m.HashSet()

  // @TODO: probably not needed with the `transformed` map below
  val refinedSymbols: m.Set[Symbol] = new m.HashSet()

  /**
   * A map that stores trees whose refinement has already been computed
   * due to a lazy type (refinement inference).
   *
   * Not for effect inference, since computing effects is done by a
   * traverser, there's no transformer involved.
   */
  val transformed: m.Map[Symbol, Tree] = new m.HashMap()

  /**
   * Caches the result of `computeEffect` on the `rhs` of a DefDef
   * or ValDef. It is used to avoid calling `computeEffect` twice
   * on the same tree. It's used in two fashions:
   *  - to obtain the result of a previous `computeEffect`
   *  - to check if `computeEffect` has already been run before
   *    looking at `rhs.tpe`
   */
  // val rhsEffect: m.Map[Symbol, Elem] = new m.HashMap()

  /**
   * ******************
   * ABSTRACT MEMBERS
   * *****************
   */

  val lattice: L
  type Elem = lattice.Elem

  /**
   * Wee need to know which annotations denote the effects of this system.
   * The inference algorithm needs to be able to remove intermediate
   * effect annotations, it removes annotations that have a type symbol
   * found in this list.
   */
  val annotationClasses: List[Symbol]
  val effectTrait: Symbol = definitions.getClass("scala.annotation.effects.Effect")

  /**
   * *************
   * ANNOTATIONS
   * ************
   */

  /**
   * @TODO: treat `@pure` here, i.e. let every subclass decide how to handle it?
   * or assign `lattice.bottom` directly in the EffectInferencer?
   */
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem]
  def fromAnnotation(tpe: Type): Option[Elem] = fromAnnotation(tpe.finalResultType.annotations)

  def toAnnotation(elem: Elem): AnnotationInfo

  val inferAnnotation = definitions.getClass("scala.annotation.effects.infer")
  val refineAnnotation = definitions.getClass("scala.annotation.effects.refine")
  val pureAnnotation = definitions.getClass("scala.annotation.effects.pure")

  /**
   * *********
   * HELPERS
   * ********
   */

  /**
   * Remove from `tp` all annotations whose annotation
   * class symbol is present in the list `cls`.
   */
  def removeAnnotations(tp: Type, cls: List[Symbol]): Type = tp match {
    case AnnotatedType(annots, underlying, _) =>
      underlying.withAnnotations(annots.filterNot(ann => cls.contains(ann.atp.typeSymbol)))
    case tp => tp
  }
  
  def removeEffectAnnotations(tp: Type): Type = tp match {
    case AnnotatedType(annots, underlying,  _) =>
      underlying.withAnnotations(annots.filterNot(ann => ann.atp.typeSymbol.isSubClass(effectTrait) || ann.atp.typeSymbol == pureAnnotation))
    case tp => tp
  }

  /**
   * Change the result type of `tp` using the function `op`.
   */
  def onResultType(tp: Type, op: Type => Type): Type = tp match {
    case MethodType(args, res) => copyMethodType(tp, args, onResultType(res, op))
    case PolyType(targs, res) => PolyType(targs, onResultType(res, op))
    case NullaryMethodType(res) => NullaryMethodType(onResultType(res, op))
    case tp => op(tp)
  }

  /**
   * Returns a the type `tp` with effect annotation `annot`.
   */
  def typeWithEffect(tp: Type, annot: AnnotationInfo): Type = {
    onResultType(tp, rt => {
      removeAnnotations(rt, annotationClasses).withAnnotation(annot)
    })
  }

  /**
   * Returns a the type `tp` with effect annotation `effect`.
   */
  def typeWithEffect(tp: Type, effect: Elem): Type = {
    typeWithEffect(tp, toAnnotation(effect))
  }

  /**
   *  Updates the effect annotation on `method` to `annot`.
   */
  def updateEffect(method: Symbol, annot: AnnotationInfo) {
    method.updateInfo(typeWithEffect(method.tpe, annot))
  }

  /**
   * Updates the effect annotation on `method` to `effect`.
   */
  def updateEffect(method: Symbol, effect: Elem) {
    updateEffect(method, toAnnotation(effect))
  }

  /**
   * Updates the result type of `tp` to `res`, while keeping
   * all annotations of the original result type.
   */
  def typeWithResult(tp: Type, res: Type): Type = {
    onResultType(tp, oldRes => {
      res.withAnnotations(oldRes.annotations)
    })
  }

  /**
   * Adds the latent effect `effect` to the function type `funTp` by creating
   * (or modifying) a RefinementType.
   *
   * Example:
   *  funTp : () => Int
   *  effect: Eff
   *  result: (() => Int) { def apply(): Int @eff }
   */
  def functionTypeWithEffect(funTp: Type, effect: Elem, owner: Symbol, pos: Position): Type = {
    import definitions.FunctionClass
    funTp match {
      case TypeRef(_, sym, refArgs) if sym == FunctionClass(refArgs.length - 1) =>
        val decls = new Scope
        val res = refinedType(List(funTp), owner, decls, pos)
        val refinementOwner = res.typeSymbol
        val method = refinementOwner.newMethod(pos, nme.apply)
        decls.enter(method)

        val (argtps, List(restp)) = refArgs.splitAt(refArgs.length - 1)
        val args = method.newSyntheticValueParams(argtps)
        val methodType = MethodType(args, typeWithEffect(restp, effect))
        method.setInfo(methodType)

        res

      case refType @ RefinedType(parents, decls) =>
        val method = decls.lookup(nme.apply)
        assert(method != NoSymbol, "unexpected refinement: "+ refType)

        // cloning the symbol / scope, so that the returned type is not == to `funTp`
        val cloned = method.cloneSymbol
        cloned.setInfo(typeWithEffect(cloned.tpe, effect))
        val newDecls = new Scope
        newDecls.enter(cloned)
        copyRefinedType(refType, parents, newDecls)

      case t =>
        abort("Function tree with unexpecte type " + t)
    }
  }

  /**
   * Changes the result type of the function type `funTp` to `restpe`.
   * Handles refined function types correctly.
   * 
   * Example:
   *   funTp  = (() => Int) { def apply(): Int @noEff }
   *   restp  = String
   *   result = (() => String) { def apply(): String @noEff }
   */
  def functionTypeWithResult(funTp: Type, restpe: Type): Type = {
    import definitions.FunctionClass
    funTp match {
      case TypeRef(pre, sym, args) if sym == FunctionClass(args.length - 1) =>
        typeRef(pre, sym, args.dropRight(1) :+ restpe)

      case refType @ RefinedType(List(TypeRef(pre, sym, args)), decls) if sym == FunctionClass(args.length - 1) =>
        val newArgs = args.dropRight(1) :+ restpe

        val method = decls.lookup(nme.apply)
        assert(method != NoSymbol, "unexpected refinement: "+ refType)

        val cloned = method.cloneSymbol
        cloned.setInfo(typeWithResult(cloned.tpe, restpe))
        val newDecls = new Scope
        newDecls.enter(cloned)
        copyRefinedType(refType, List(typeRef(pre, sym, newArgs)), newDecls)

      case t =>
        abort("Function tree with unexpecte type " + t)
    }
  }

  /**
   * Return the result type argument of the function type `funTp`.
   */
  def resultTypeArgument(funTp: Type): Type = {
    import definitions.FunctionClass
    funTp match {
      case TypeRef(_, sym, args) if sym == FunctionClass(args.length - 1) =>
        args.last
      case RefinedType(List(TypeRef(_, sym, args)), _) if sym == FunctionClass(args.length - 1) =>
        args.last
      case t => abort("not a function type: " + t)
    }
  }

  /**
   * ************************
   * CHECKER TRANSFORMATION
   * ***********************
   */

  /**
   * Checks effect conformance
   *  - Method's effect conforms to effect annotation on return type
   *  - Conformance of refinement types with effect annotations
   */
  class Checker(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case dd@DefDef(_, _, _, _, _, rhs) if !rhs.isEmpty =>
          val td = super.transform(dd).asInstanceOf[DefDef]
          checkDefDef(td, localTyper, currentOwner, unit)

        case vd@ValDef(_, _, _, rhs) if !rhs.isEmpty =>
          val td = super.transform(vd).asInstanceOf[ValDef]
          checkValDef(td, localTyper, currentOwner, unit)

        case _ =>
          super.transform(tree)
      }
    }
  }

  /**
   * Check a DefDef tree
   *  - that effect of the body conforms to the annotated effect
   *  - that the type of the body conforms to the annotated type
   *  - that no type or effect is larger than from an overridden method
   *
   * @TODO: do nothing if return type is "Unit", just return the DefDef
   */
  def checkDefDef(dd: DefDef, typer: Typer, owner: Symbol, unit: CompilationUnit): DefDef = {
    val sym = dd.symbol

    val symEff = fromAnnotation(sym.tpe).getOrElse(abort("no latent effect annotation on " + sym))
    val symTp = sym.tpe.finalResultType // @TODO: what about type parameters? def f[T](x: T): T = x

    if (!inferEffect(sym)) {
      // Check or infer the latent effect
      val rhsEff = computeEffect(sym, dd.rhs, typer, owner, unit)
      if (!lattice.lte(rhsEff, symEff))
        effectError(dd, symEff, rhsEff)
    }

    /**
     * Note that "computeEffect" might call "refine" on the rhs, and put the
     * result into the "transformed" map. This makes the followin example work:
     *
     *   def f: (() => Int) @infer @refine = () => 1
     *   def v: Int @noEff = f.apply()
     *
     * Initial type checking assigns the symbol "Function0.apply" to "f.apply",
     * which has the maximal effect. Calling "refine" on the rhs assings to
     * "f.apply" the symbol "<refinement>.apply", which is pure.
     */

    val refinedRhs =
      if (refineType(sym) || sym.isConstructor) {
        // @TODO: assert(transformed.contains(sym)) ??? probably false for constructors
        transformed.getOrElse(sym, dd.rhs)
      } else {
        // Check or infer the return type
        val rhs1 = transformed.getOrElseUpdate(sym, refine(dd.rhs, typer, owner, unit))
        checkRefinement(dd, rhs1.tpe, symTp)
        rhs1
      }

    // check the latent effect and return type for all overridden methods
    for (os <- sym.allOverriddenSymbols) {
      // @TODO: lattice.top when overridden does not have an effect annotation?
      val overriddenEffect = fromAnnotation(os.tpe).getOrElse(lattice.top)
      if (!lattice.lte(symEff, overriddenEffect))
        overrideError(dd, os, overriddenEffect, symEff)
      checkRefinement(dd, os.tpe.finalResultType, symTp)
    }

    treeCopy.DefDef(dd, dd.mods, dd.name, dd.tparams, dd.vparamss, dd.tpt, refinedRhs)

    /*    val rhsEffOpt =
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
        if (dd.rhs.isEmpty || refinedSymbols(sym)) None
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
    } */
  }

  def checkValDef(vd: ValDef, typer: Typer, owner: Symbol, unit: CompilationUnit): ValDef = {
    val sym = vd.symbol

    val symTp = sym.tpe

    val refinedRhs =
      if (refineType(sym)) {
        // @TODO: assert(transformed.contains(sym)) ???
        transformed.getOrElse(sym, vd.rhs)
      } else {
        // Check or infer the return type
        val rhs1 = transformed.getOrElseUpdate(sym, refine(vd.rhs, typer, owner, unit))
        checkRefinement(vd, rhs1.tpe, symTp)
        rhs1
      }

    for (os <- sym.allOverriddenSymbols) {
      checkRefinement(vd, os.tpe, symTp)
    }

    treeCopy.ValDef(vd, vd.mods, vd.name, vd.tpt, refinedRhs)

    /*
    val rhsTpOpt =
      if (vd.rhs.isEmpty || refinedSymbols(sym)) None
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
*/
  }

  def checkRefinement(tree: Tree, tp1: Type, tp2: Type) {
    /**
     * InferMode enables the AnnotationCheckers for checking
     * refinements, e.g. to compare the following:
     *   tp1 = (Int => Int) { def apply(x: Int): Int @noEff }
     *   tp2 = (Int => Int) { def apply(x: Int): Int @eff }
     *
     * in `def foo: tp2 = (...): tp1`
     * 
     * BUT: types of trees (tp1) do NOT have latent effects!
     * E.g. in `def foo: Int @noEff = 1`, we get
     *   tp1 = ConstantType(Int(1))
     *   tp2 = Int @noEff
     *
     * => Need to remove latent effects.
     */
    val (tp1a, tp2a) = (removeEffectAnnotations(tp1), removeEffectAnnotations(tp2))
    if (!annotationChecker.localInferMode(tp1a <:< tp2a)) {
      refinementError(tree, tp2a, tp1a)
    }
  }

  /**
   * ***********************
   * COMPUTING REFINEMENTS
   * **********************
   */

  /**
   * Computes the (refined) type of `rhs` and returns the type
   * type `origTp` with this refined result type, while keeping
   * existing annotations.
   */
  def computeType(sym: Symbol, rhs: Tree, origTp: Type, typer: Typer, owner: Symbol, unit: CompilationUnit): Type = {
    // computeType can be called multiple times (value, getter, setter)
    val refined = transformed.getOrElseUpdate(sym, refine(rhs, typer, owner, unit))

    val packed = typer.packedType(refined, sym)
    val widened = typer.namer.widenIfNecessary(sym, packed, WildcardType)

    onResultType(origTp, tp => widened.withAnnotations(tp.annotations))
  }

  def refine(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): Tree = {
    val refiner = new RefineTransformer(unit, typer, owner, tree)
    refiner.refine()
  }

  // @TODO: maybe have anoter parameter "pt", which will be used for re-type-to
  class RefineTransformer(unit: CompilationUnit, typer: Typer, owner: Symbol, tree: Tree) extends TypingTransformer(unit) {
    localTyper = typer
    currentOwner = owner

    var result = tree

    def refine(): Tree = {
      result = transform(result)
      val res = localTyper.typed(result)
      /**
       * Effect annotations on the trees make no sense:
       *   def foo(x: Int): Int @noEff = x
       *   def bar: Int @refine = foo(1)
       * "bar" would have both effect "@eff" (public method) and "@noEff"
       * (because the computed type of "foo(1)" is "Int @noEff")
       * 
       * @TODO: it's a bit unsystematic to do it only here (the outermost
       * node of the tree), maybe we should have a traverser deleting all
       * annotatinos in trees.
       */
      res.tpe = removeEffectAnnotations(res.tpe)
      res
    }

    protected def untypeTo(stop: Tree, untypeStop: Boolean = false) {
      // transformer because it might remove some "TypeApply" nodes
      result = new ResetTransformer(stop, untypeStop).transform(result)
    }

    protected def untypeIfRefined(tree: Tree): Tree = {
      val sym = tree.symbol
      // for fields, the symbol of Select is the getter, while refineType contains the field
      if (refineType(sym) || (sym.isGetter && refineType(sym.accessed))) {
        untypeTo(tree, true)
      }
      tree
    }

    override def transform(tree: Tree): Tree = tree match {
      /* skipped by `transformStats`
      case ClassDef(_, _, _, _)     => tree
      case ModuleDef(_, _, _)       => tree
      case DefDef(_, _, _, _, _, _) => tree
      case ValDef(_, _, _, _)       => tree
      */

      case Function(params, body) =>
        val sym = tree.symbol
        val refinedBody = transformed.getOrElseUpdate(sym, EffectChecker.this.refine(body, localTyper, owner, unit))

        /**
         * Concequence of Effects being TypeConstraints
         *   def foo: Int @noEff @noXio = 1
         *   val x = () => { eff(); foo }
         * ==> x: (() => Int @noXio @noEff){def apply(): Int @noXio @eff}
         * Therefore, remove effect annotations
         */

        val restpe = localTyper.packedType(refinedBody, tree.symbol).deconst
        val funtpe =
          if (restpe == resultTypeArgument(tree.tpe)) tree.tpe
          else functionTypeWithResult(tree.tpe, restpe)

        val eff = computeEffect(sym, refinedBody, localTyper, owner, unit)
        val refinedType = functionTypeWithEffect(funtpe, eff, currentClass, tree.pos)
        if (refinedType != funtpe) {
          tree.tpe = refinedType
          untypeTo(tree)
        }

        treeCopy.Function(tree, params, refinedBody)

      case Select(qual, name) =>
        untypeIfRefined(tree)
        super.transform(tree)

      case Ident(name) =>
        untypeIfRefined(tree)
        super.transform(tree) // probably not needed, but well

      case _ =>
        super.transform(tree)
    }

    /**
     * Statements have no influence on typing
     */
    override def transformStats(stats: List[Tree], owner: Symbol): List[Tree] = stats

    /**
     * A Transformer that removes types and symbols on the path to the tree `stop`.
     */
    private class ResetTransformer(stop: Tree, untypeStop: Boolean) extends Transformer {
      private val trace: m.Stack[Tree] = new m.Stack()

      private def reset(tree: Tree) {
        if (tree.hasSymbol) tree.symbol = NoSymbol
        tree match {
          case EmptyTree => // tpe_= throws an exception
            ()
          case tt@TypeTree() =>
            if (tt.wasEmpty) tt.tpe = null
          case _ =>
            tree.tpe = null
        }
      }

      private def synteticTargs(targs: List[Tree]) = false // @TODO (find out if targs were inferred)

      override def transform(tree: Tree): Tree = {
        if (tree == stop) {
          if (untypeStop) trace.push(tree)
          for (t <- trace)
            reset(t)
          tree
        } else tree match {
          case TypeApply(fun, targs) if synteticTargs(targs) =>
            super.transform(fun)
          case _ =>
            trace.push(tree)
            super.transform(tree)
            trace.pop()
        }
      }
    }

  }

  /*
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
      refinedSymbols += sym
    }
  }
*/

  /**
   * Returns the type of `sym` by applying effect type
   * inference before when necessary.
   */
  /*
  def typeOf(sym: Symbol): Type = {
    maybeInferType(sym)
    sym.tpe
  }
*/

  /**
   * *******************
   * COMPUTING EFFECTS
   * ******************
   */

  /**
   * Compute and return the effect caused by executing `tree`
   */
  def computeEffect(sym: Symbol, tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit) = {
    val refinedTree = transformed.getOrElseUpdate(sym, refine(tree, typer, owner, unit))
    newEffectTraverser(refinedTree, typer, owner, unit).compute()
  }

  def newEffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): EffectTraverser =
    new EffectTraverser(tree, typer, owner, unit)

  class EffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit) extends Traverser {
    override def apply[T <: Tree](t: T): T = abort("apply should not be called")

    def compute(): Elem = {
      acc = lattice.bottom
      traverse(tree)
      acc
    }

    protected var acc: Elem = lattice.bottom
    protected def add(eff: Elem) { acc = lattice.join(acc, eff) }

    override def traverse(tree: Tree) {
      tree match {
        case ClassDef(_, _, _, _) => ()
        case ModuleDef(_, _, _) => ()
        case DefDef(_, _, _, _, _, _) => ()
        case ValDef(_, _, _, _) if tree.symbol.isLazy => ()
        case TypeDef(_, _, _, _) => ()
        case Function(_, _) => ()

        /**
         * @TODO on Select and Ident
         *  - effect of module constructor!!! (happens when module is accessed for the first time)
         *  - lazy vals (vals are in constructor, but lazy not (?))
         */
        case Apply(_, _) =>
          val (fun, targs, argss) = decomposeApply(tree)
          traverseQual(fun)
          traverseTrees(targs)
          for (args <- argss) traverseTrees(args)
          add(computeApplicationEffect(fun, targs, argss))

        case TypeApply(_, _) =>
          val (fun, targs, Nil) = decomposeApply(tree)
          traverseQual(fun)
          traverseTrees(targs)
          add(computeApplicationEffect(fun, targs))

        case Select(qual, _) =>
          traverse(qual)
          if (tree.symbol.isMethod)
            add(computeApplicationEffect(tree))

        case Ident(_) =>
          if (tree.symbol.isMethod)
            add(computeApplicationEffect(tree))

        case _ =>
          super.traverse(tree)
      }
    }

    protected def decomposeApply(tree: Tree): (Tree, List[Tree], List[List[Tree]]) = {
      var baseFun: Tree = null
      var targs: List[Tree] = Nil
      def apply0(t: Tree): List[List[Tree]] = t match {
        case Apply(fun, args) =>
          args :: apply0(fun)
        case TypeApply(fun, targs0) =>
          targs = targs0
          apply0(fun)
        case _ =>
          baseFun = t
          Nil
      }
      val argss = apply0(tree)
      (baseFun, targs, argss.reverse)
    }

    protected def traverseQual(tree: Tree) {
      tree match {
        case Select(qual, _) => traverse(qual)
        case Ident(_) => ()
      }
    }

    protected def computeApplicationEffect(fun: Tree, targs: List[Tree] = Nil, argss: List[List[Tree]] = Nil) = {
      var res = applicationEffect(fun, targs, argss, typer.context1)
      for (t <- appEffectTransformers) {
        val trans = t(res, fun, targs, argss, typer.context1)
        res = trans // t(res, fun, targs, argss, typer.context1)
      }
      res
    }
  }

 /**
  * PCTracking adapts the effect of an application expression.
  */
  def addAppEffectTransformer(f: (Elem, Tree, List[Tree], List[List[Tree]], Context) => Elem) {
    appEffectTransformers += f
  }
  private val appEffectTransformers = m.ListBuffer[(Elem, Tree, List[Tree], List[List[Tree]], Context) => Elem]()

  /**
   * Compute the effect of a function application. This method exists outside the
   * EffectTraverser so that it can be easily overridden by concrete checkers.
   */
  def applicationEffect(fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context)  = {
    val sym = fun.symbol
    val eff = fromAnnotation(sym.tpe) // will complete lazy type if necessary
    // println("effect of applying "+ sym +": "+ eff)
    eff.getOrElse(lattice.top) // @TODO: top by default?
  }

  /*
  def maybeInferEffect(method: Symbol) {
    if (inferEffect.contains(method) && fromAnnotation(method.tpe).isEmpty) {
      val rhs = inferEffect(method).rhs
      updateEffect(method, rhsEffect.getOrElseUpdate(method, computeEffect(rhs)))
    }
  }
*/

  /**
   * Returns the latent effect of `method` by applying
   * effect inference before when necessary.
   */
  /*
  def effectOf(method: Symbol): Option[Elem] = {
    maybeInferEffect(method)
    fromAnnotation(method.tpe)
  }
*/

  /**
   * *************
   * INTEGRATION
   * ************
   */

  def newTransformer(unit: CompilationUnit) = {
    this.unit = unit
    new Checker(unit)
  }

  /**
   * Add an AnnotationChecker to influence `lub` and `glb` computations
   */
  val annotationChecker = new AnnotationChecker {
    override val inferenceOnly = true

    def annotationsConform(tpe1: Type, tpe2: Type) = {
      val eff1 = fromAnnotation(tpe1.annotations).getOrElse(lattice.top)
      val eff2 = fromAnnotation(tpe2.annotations).getOrElse(lattice.top)
      lattice.lte(eff1, eff2)
    }
  }
  global.addAnnotationChecker(annotationChecker)

  /**
   * Useful for error reporting
   */
  var unit: CompilationUnit = _

  /**
   * This method is called when the actual effect of a method does not conform
   * to the annotated one.
   */
  def effectError(tree: Tree, expected: Elem, found: Elem) {
    unit.error(tree.pos, "latent effect mismatch;\n found   : " + found + "\n required: " + expected)
  }

  /**
   * This method is called when an overriding method has a larger
   * effect than the overridden one.
   */
  def overrideError(tree: Tree, overridden: Symbol, expected: Elem, found: Elem) {
    effectError(tree, expected, found)
  }

  def refinementError(tree: Tree, expected: Type, found: Type) {
    unit.error(tree.pos, "effect type mismatch;\n found   : " + found + "\n required: " + expected)
  }

}
