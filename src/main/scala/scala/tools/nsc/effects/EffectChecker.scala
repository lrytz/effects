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
   * Contains method symbols for which the latent effect has to be inferrred.
   * See method `inferEffect` for more details.
   */
  val inferEffect: m.Set[Symbol] = new m.HashSet()

  /**
   * Contains symbols whose type might change, i.e. become refined type with
   * effect annotations in the refinement.
   *
   * For example, in
   * 
   *   val a = (x: Int) => throw E
   * 
   * the type of `a` changes from `Int => Nothing` to
   * `Int => Nothing { def apply(x: Int) => Nothing @throws[E] }`
   *
   * Another example: In
   * 
   *   trait C { def foo(): Int }
   *   val x = new C { def foo() = 1 }
   * 
   * the type of `x` changes from `C` to `C { def foo(): Int @pure }`
   */
  val refineType: m.Set[Symbol] = new m.HashSet()

  // @TODO: probably not needed with the `transformed` map below
  // val refinedSymbols: m.Set[Symbol] = new m.HashSet()

  /**
   * A map that stores `rhs` trees of ValDef and DefDef, that have been transformed
   * by the `refine` function.
   * 
   * The reason we need this map: The EffectInferencer assigns lazy types to symbols
   * that obtain refined types (due to effect inference), see its docs. Computing these
   * refined types uses the `refine` function, which changes (transforms) `rhs` trees.
   * 
   * Because completion of lazy types happens on demand, the resulting trees cannot
   * be put pack into the tree. Therefore they are stored in this map.
   * 
   * Afterwards, the `Checker` transformer basically applies the `refine` transformation
   * on the entire tree, but it re-uses the results in this map if available.
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
   * @implement
   * 
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
   * @implement
   * 
   * @TODO: treat `@pure` here, i.e. let every subclass decide how to handle it?
   * or assign `lattice.bottom` directly in the EffectInferencer?
   * 
   * later: probably better to let each effect checker handle it itself. maybe some
   * effect system wants to treat a combination of @prue and other annotations.
   */
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem]
  def fromAnnotation(tpe: Type): Option[Elem] = fromAnnotation(tpe.finalResultType.annotations)

  /**
   * @implement
   */
  def toAnnotation(elem: Elem): List[AnnotationInfo]

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
  def typeWithEffect(tp: Type, annots: List[AnnotationInfo]): Type = {
    onResultType(tp, rt => {
      removeAnnotations(rt, annotationClasses).withAnnotations(annots)
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
  def updateEffect(method: Symbol, annot: List[AnnotationInfo]) {
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
   *  
   * @param owner is the owner of the newly created refinement class symbol. (@TODO: not
   *   sure what it should be.. just the next enclosing owner? or the enclosing class?)
   * 
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
   * The Checker is the main traversal of this phase (see method `newTransformer` at the
   * end of this file to see how it's integrated). It traverses the entire program and
   * checks conformance of side-effects:
   *  - The effect of a method body has to conform to the effect annotation on the
   *    methods return type
   *  - For methods and values with a refined (return) type, it checks that the type
   *    of the righthand-side conforms to the annotated one (including effect annotations
   *    inside the refinement)
   * 
   * The Checker applies the `refine` transformation to all righthand sides of method
   * and value definitions, and therefore it is itself a (typing) transformer. See doc
   * in class EffectInferencer.
   *  
   * @TODO: should it also look at `Typed` trees?
   */
  class Checker(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case dd@DefDef(_, _, _, _, _, rhs) if !rhs.isEmpty =>
          // @TODO: could probably also call first `checkDefDef` and then
          // feed the result in `super.transform`. then no need for a cast.
          val td = super.transform(dd).asInstanceOf[DefDef]
          atOwner(td.symbol) {
            // @TOOD: like in the EffectInferencer, don't we have to do `reenterTypeParams` and `reenterValueParams`?
            // because `checkDefDef` calls `refine`, which does the re-type-checking thing. => test it!
            checkDefDef(td, localTyper, unit)
          }

        case vd@ValDef(_, _, _, rhs) if !rhs.isEmpty =>
          val td = super.transform(vd).asInstanceOf[ValDef]
          atOwner(td.symbol) {
            checkValDef(td, localTyper, unit)
          }

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
  def checkDefDef(dd: DefDef, ddTyper: Typer, unit: CompilationUnit): DefDef = {
    val sym = dd.symbol

    val symEff = fromAnnotation(sym.tpe).getOrElse(abort("no latent effect annotation on " + sym))
    val symTp = sym.tpe.finalResultType // @TODO: what about type parameters? def f[T](x: T): T = x

    if (!inferEffect(sym)) {
      // Check or infer the latent effect
      if (sym.toString() == "method modify")
        println()
      val rhsEff = computeEffect(dd.rhs, ddTyper, sym, unit)
      if (!lattice.lte(rhsEff, symEff))
        effectError(dd, symEff, rhsEff)
    }

    /* Note that "computeEffect" might call "refine" on the rhs, and put the
     * result into the "transformed" map, see comment on `computeEffect`.
     */

    val refinedRhs =
      if (refineType(sym) || sym.isConstructor) {
        // @TODO: assert(transformed.contains(sym)) ??? probably false for constructors
        // why not call `refine` in getOrElse? because we know it has already been called
        // above when looking at `sym.tpe`?
        transformed.getOrElse(sym, dd.rhs)
      } else {
        // Check or infer the return type
        val rhs1 = refine(dd.rhs, ddTyper, sym, unit)
        checkRefinement(dd, rhs1.tpe, symTp)
        rhs1
      }

    // check the latent effect and return type for all overridden methods
    for (os <- sym.allOverriddenSymbols) {
      // @TODO: lattice.top when overridden does not have an effect annotation? more conservative would be lattice.bottom.
      val overriddenEffect = fromAnnotation(os.tpe).getOrElse(lattice.top)
      if (!lattice.lte(symEff, overriddenEffect))
        overrideError(dd, os, overriddenEffect, symEff)
      checkRefinement(dd, symTp, os.tpe.finalResultType)
    }

    treeCopy.DefDef(dd, dd.mods, dd.name, dd.tparams, dd.vparamss, dd.tpt, refinedRhs)
  }

  /**
   * Check a DefDef tree
   *  - that the type of the rhs conforms to the annotated type
   *  - that no type is larger than from an overridden method
   */
  def checkValDef(vd: ValDef, vdTyper: Typer, unit: CompilationUnit): ValDef = {
    val sym = vd.symbol

    val symTp = sym.tpe

    val refinedRhs =
      if (refineType(sym)) {
        // @TODO: assert(transformed.contains(sym)), because we looked at sym.tpe???
        transformed.getOrElse(sym, vd.rhs)
      } else {
        // Check or infer the return type
        val rhs1 = refine(vd.rhs, vdTyper, sym, unit)
        checkRefinement(vd, rhs1.tpe, symTp)
        rhs1
      }

    for (os <- sym.allOverriddenSymbols) {
      checkRefinement(vd, symTp, os.tpe)
    }

    treeCopy.ValDef(vd, vd.mods, vd.name, vd.tpt, refinedRhs)
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
     * 
     * @TODO (later): since now we have `packedTypeAdaptAnnotations`, do we
     * still need to call `removeEffectAnnotations` here?
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
   * Computes the (refined) type of `rhs` and returns the type type `origTp` with
   * this refined result type, while keeping existing annotations.
   * 
   * @param rhs        The tree for which to compute the type. It has to be the righthand
   *                   side of a DefDef or ValDef tree
   * @param origTp
   * @param rhsTyper   The local typer which has the right context for typing `rhs`
   * @param sym        The symbol of the definition of `rhs`
   * @param unit  
   */
  def computeType(rhs: Tree, origTp: Type, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): Type = {
    // computeType can be called multiple times (value, getter, setter). Results are stored in
    // the `transformed` map, see method `refine`.
    val refined = refine(rhs, rhsTyper, sym, unit)

    val packed = rhsTyper.packedType(refined, sym)
    val widened = rhsTyper.namer.widenIfNecessary(sym, packed, WildcardType)

    onResultType(origTp, tp => widened.withAnnotations(tp.annotations))
  }

  /**
   * Pass the tree `rhs` through the RefineTransformer, if it has not yet been transformed
   * before and stored in the `transformed` map.
   * 
   * @param rhs        The `rhs` tree of a DefDef or ValDef
   * @param rhsTyper   A typer instance with the right context for typing `rhs`
   * @param sym        The symbol of the definition of `rhs`
   * @param unit
   */
  def refine(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): Tree = {
    transformed.getOrElseUpdate(sym, {
      val refiner = new RefineTransformer(rhs, rhsTyper, sym, unit)
      refiner.refine()
    })
  }

  /**
   * During effect inference, some symbols acquire more specific (refined) types. For
   * exmple, the methods
   * 
   *   val foo: (Int => Int) @refine = (x: Int) => x
   *   
   * has type `Int => Int` after ordinary type-checking. Effect inference assigns to
   * it a refinement type `(Int => Int){ def apply(x: Int): Int @pure }`.
   * 
   * This change of type influences the side-effect that is computed for code which
   * uses `foo`. Take the following method:
   * 
   *   def bar: Int @infer = foo.apply(10)
   * 
   * When computing the side-effect, we look at the symbol of `foo.apply`. Again,
   * ordinary type-checking resolved this selection to the symbol `Function1.apply`.
   * Using this, we would conclude the maximal side-effect for that application.
   * 
   * The `RefineTransformer` updates all references to symbols with refined types.
   * It does so by removing symbol and type information from the tree and running
   * the type-checker agian on sub-trees to the selection.
   * 
   * After the refine-transformer, the selection `foo.apply` will have symbol
   * `<refinement>.apply` (refinement type above). Therefore, effect checking can
   * conclude that applying this function is pure.
   * 
   * A special treatment is given to anonymous function trees, see comment below.
   */
  class RefineTransformer(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends TypingTransformer(unit) {
    localTyper = rhsTyper
    currentOwner = sym

    def refine(): Tree = {
      val refined = transform(rhs)
      val untyped = new ResetTransformer(untypeTargets).reset(refined)

      val res = localTyper.typed(untyped)
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
       * 
       * @TODO 2: this should now no longer be necessary, because the
       * AnnotationChecker now implements `packedTypeAdaptAnnotations`.
       */
      // res.tpe = removeEffectAnnotations(res.tpe)
      res
    }

    protected val untypeTargets: m.Set[(Tree, Boolean)] = new m.HashSet()

    protected def untypeTo(stop: Tree, untypeStop: Boolean = false) {
      untypeTargets += ((stop, untypeStop))
    }

    protected def untypeIfRefined(tree: Tree): Tree = {
      val sym = tree.symbol
      // for fields, the symbol of Select is the getter, while refineType contains the field
      if (refineType(sym) || (sym.isGetter && refineType(sym.accessed))) {
        untypeTo(tree, true)
      } else if (atPhase(currentRun.typerPhase)(sym.tpe) != sym.tpe) {
        /* Catch symbols defined in a previous compiler-run (interpreter) that were refined.
         * They don't appear in the `refineType` map for this run. However, they still change
         * type, because the type history is kept and just updated to the new run. So even in
         * the new run, at typer phase, these symbols are still not-refined, but they are
         * refaned later (now).
         * 
         * @TODO: solve this more nicely.
         */
        untypeTo(tree, true)
      }

      tree
    }

    override def transform(tree: Tree): Tree = tree match {
      /* already skipped by `transformStats`
      case ClassDef(_, _, _, _)     => tree
      case ModuleDef(_, _, _)       => tree
      case DefDef(_, _, _, _, _, _) => tree
      case ValDef(_, _, _, _)       => tree
      */
      
      /**
       * Like the type of a `Select` node can change (select something whose type changes),
       * the type of a `Function` can change as well. There are two things that can change:
       * 
       *   - the return type of the function, e.g. in `() => foo`, if the type of `foo` is,
       *     refined, then the return type of the function changes.
       *   - the type of the function can become a refinement, e.g. `() => 1` has first type
       *   `() => Int`, then becomes `(() => Int) { def apply(): Int @pure }`
       * 
       * To find the first, we call `refine` on the body of the function and extract the
       * type of the resulting tree.
       * For the second, we call `computeEffect` on the function body and incorporate the
       * effect annotation in the function type, using a refinement.
       * 
       * Just as with a `Select` that becomes a more specific type, we re-typecheck the part
       * of the tree up to that `Function` node to take in account its more specific type.
       */
      case Function(params, body) =>
        val funSym = tree.symbol
        val funTyper = atOwner(funSym)(localTyper)
        
        // @TOOD do we need to do reenterType/ValueParams? see EffectInferencer, comment in checkDefDef...
        val refinedBody = EffectChecker.this.refine(body, funTyper, funSym, unit)

        /**
         * Concequence of Effects being TypeConstraints
         *   def foo: Int @noEff @noXio = 1
         *   val x = () => { eff(); foo }
         * ==> x: (() => Int @noXio @noEff){def apply(): Int @noXio @eff}
         * Therefore, remove effect annotations (done in `refine`)
         */

        val restpe = localTyper.packedType(refinedBody, funSym).deconst
        val funtpe =
          if (restpe == resultTypeArgument(tree.tpe)) tree.tpe
          else functionTypeWithResult(tree.tpe, restpe)

        val eff = computeEffect(refinedBody, funTyper, funSym, unit)
        // @TODO the owner of the newly created `<refinement>` class symbol is `currentClass`. not sure if this is correct..
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
     * 
     * @TODO: sure that's correct? what if a statement refers to a symbol whose type
     * is being refined, then that should be updated before computing the effect, no?
     */
    override def transformStats(stats: List[Tree], owner: Symbol): List[Tree] = stats

    /**
     * A Transformer that removes types and symbols on the path to the tree `stop`.
     *
     * Transformer (not traverser) because it might remove some "TypeApply" nodes.
     */
    private class ResetTransformer(stops: m.Set[(Tree, Boolean)]) extends Transformer {
      private val toUntype: m.Set[Tree] = new m.HashSet()
      private val trace: m.Stack[Tree] = new m.Stack()

      def reset(tree: Tree) = {
        val res = transform(tree)
        for (t <- toUntype)
          untype(t)
        res
      }
      
      private def untype(tree: Tree) {

        /**
         * For Select, if the selected symbol is a method, we need to erase it.
         * Re-typechecking might assign a different symbol, namely when there's
         * a refinement inferred. Example
         *
         *   val a: (() => Int) @refine = () => Int
         *   def f = a.apply()
         *
         * Initially, we get the symbol "Function0.apply", which has all effect.
         * However, the type of "a" is refined, and re-typechecking gives the
         * symbol "<refinement>.apply", which has no effect.
         */
        tree match {
          case Select(_, _) if tree.symbol.isMethod => tree.symbol = NoSymbol
          case _ => ()
        }

        tree match {
          case EmptyTree => // tpe_= throws an exception on EmptyTree
            ()
          case tt@TypeTree() =>
            if (tt.wasEmpty) tt.tpe = null
          case _ =>
            tree.tpe = null
        }
      }

      private def synteticTargs(targs: List[Tree]) = false // @TODO (find out if targs were inferred)

      override def transform(tree: Tree): Tree = {
        stops.find(p => p._1 == tree) match {
          case Some((_, untypeStop)) =>
            if (untypeStop) trace.push(tree)
            toUntype ++= trace
            tree
          case _ => tree match {
            case TypeApply(fun, targs) if synteticTargs(targs) =>
              super.transform(fun)
            case _ =>
              trace.push(tree)
              val t = super.transform(tree)
              trace.pop()
              t
          }
        }
      }
    }

  }



  /**
   * *******************
   * COMPUTING EFFECTS
   * ******************
   */

  /**
   * Compute and return the effect caused by executing `tree`.
   * 
   * We first have to call `refine` on `tree` because computing the refined types
   * can influence the effect of the result. Example:
   * 
   *   def foo(): C @refine = new C { def bar = 1 }
   *   def baz: Int @infer = foo().bar
   * 
   * Note that `refine` not only computes more precise types for functions, but also
   * assigns more precise symbols to `Select` nodes. So initially after ordinary
   * type-checking, the tree that selects `bar` has as symbol "C.bar". However,
   * after calling `refine`, that Select tree gets the more precise symbol
   * `<refinement>.baz`, and `computeEffect` will find that applying this method
   * is pure.
   * 
   * @param rhs        The `rhs` tree of a DefDef or ValDef
   * @param rhsTyper   A typer instance with the right context for typing `rhs`
   * @param sym        The symbol of the definition of `rhs`
   * @param unit
   */
  def computeEffect(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) = {
    val refinedTree = refine(rhs, rhsTyper, sym, unit)
    newEffectTraverser(refinedTree, rhsTyper, sym, unit).compute()
  }

  /**
   * @implement This method can be overridden by concrete effect checkers.
   * 
   * Concrete effect checkers might implement a custom subclass of `EffectTraverser`
   * for computing effects of `rhs` trees. This factory method is called to obtain
   * EffectChecker instances.
   */
  def newEffectTraverser(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    new EffectTraverser(rhs, rhsTyper, sym, unit)

  class EffectTraverser(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends Traverser {
    override def apply[T <: Tree](t: T): T = abort("apply should not be called")

    def compute(): Elem = {
      acc = lattice.bottom
      traverse(rhs)
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
          handleApplication(tree)

        case TypeApply(_, _) =>
          handleApplication(tree)

        case Select(qual, _) =>
          if (tree.symbol.isMethod)
            handleApplication(tree)
          else
            traverse(qual)

        case Ident(_) =>
          if (tree.symbol.isMethod) {
            // a parameterless local method is applied using an `Ident` tree.
            handleApplication(tree)
          }

        // @TODO: correctly treat pattern matches. E.g. in "case C(a, b)", the case has the form
        //   CaseDef(Apply(TypeTree(), args), _, _)
        // with TypeTree().tpe = MethodType(List(a,b), C)
        case CaseDef(_, _, _) => ()

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
        case t =>
          throw new MatchError(t)
      }
    }

    /**
     * @implement This method can be overridden by effect traversers.
     * 
     * This methods decomposes the `tree`, which is a function application, into three
     * parts: the function, the type arguments, and the value argumentss. It traverses
     * all these parts (calling `add` on their effects) and finally adds the latent effect
     * of the function using `computeApplicationEffect`.
     */
    protected def handleApplication(tree: Tree) {
      val (fun, targs, argss) = decomposeApply(tree)
      traverseQual(fun)
      traverseTrees(targs)
      for (args <- argss) traverseTrees(args)
      add(computeApplicationEffect(fun, targs, argss))
    }
    
    /**
     * @implement This method can be overridden by effect traversers.
     * 
     * Extracts the latent effect of the function being applied and adapts it using
     * `adaptLatentEffect` and `adaptToPolymorphism`.
     */
    protected def computeApplicationEffect(fun: Tree, targs: List[Tree] = Nil, argss: List[List[Tree]] = Nil) = {
      val latent = latentEffect(fun, targs, argss, rhsTyper.context1)
      val adapted = adaptLatentEffect(latent, fun, targs, argss, rhsTyper.context1)
      adaptToEffectPolymorphism(adapted, fun, targs, argss, rhsTyper.context1)
    }
  }

  /**
   * @implement This method exists outside the EffectTraverser so that it can be
   * easily overridden by concrete checkers. A simple effect checker might only
   * override this method and not even implement a custom EffectTraverser. 
   * 
   * Returns the latent effect of a function application.
   */
  def latentEffect(fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) = {
    val sym = fun.symbol
    val eff = fromAnnotation(sym.tpe)
    eff.getOrElse(lattice.top)
  }

  /**
   * @implement This method can be overridden by concrete effect checkers. It allows
   * to adapt / change / customize the latent effect, which is obtained from a function's
   * effect annotation.
   */
  def adaptLatentEffect(eff: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    eff
  }
  
 /**
  * This method is overridden by PCTracking, which will adapt the effect of an application
  * expression mainly in two ways:
  *  - remove the effect if it's a parameter call
  *  - add effects caused by `@pc` annotations on `fun`
  */
  def adaptToEffectPolymorphism(latent: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    latent
  }

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
   * Add an AnnotationChecker to influence `lub` and `glb` computations, and also
   * propagation of effect annotations in refined types.
   */
  val annotationChecker = new AnnotationChecker {
    override val inferenceOnly = true

    def annotationsConform(tpe1: Type, tpe2: Type) = {
      val eff1 = fromAnnotation(tpe1.annotations).getOrElse(lattice.top)
      val eff2 = fromAnnotation(tpe2.annotations).getOrElse(lattice.top)
      lattice.lte(eff1, eff2)
    }
    
    /**
     * This method is called in `packedType`, it allows pre-processing the trees
     * (and therefore their type) before passing them to packedType. Since during
     * type inference, `packedType` is called on the rhs-type of a definition, this
     * allows us to remove incorrect effect annotations. Example:
     * 
     *   def f(i: Int): Int @pure = i + 1
     *   def g() = { doSideEffect(); f(10) }
     * 
     * When computing the return of method g, the (standard) type-checker looks at
     * the type of the rhs-tree, which in this case is `Int @pure` (pure is a TypeConstraint).
     * This is not correct, effect inference works differently.
     * 
     * The situation can be even worse, as the following example shows:
     * 
     *   abstract class A { def f(): Unit @mod(this) }
     *   def g(a: A) = { val x = a; a.f() }
     * 
     * In this case, the return type inferred for g is `Unit @mod(x) forSome { val x: A }`.
     * In order to remove this incorrect effect annotation we would even have to deal
     * with existentials. So it's much simpler to just remove effect annotations from
     * trees, since they don't make any sense there anyway.
     * 
     * @TODO: if we have multiple effect checkers, in principle its enough if one of them
     * does this. As it is now, the first one will remove all effect annotations and the
     * others just run consuming cpu, but not doing anything.
     */
    override def packedTypeAdaptAnnotations(tree: Tree, owner: Symbol): Tree = {
      val old = tree.tpe
      tree.tpe = removeEffectAnnotations(tree.tpe)
      if (old != tree.tpe) println("removed effect annotation from tree: "+ tree)
      tree
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
