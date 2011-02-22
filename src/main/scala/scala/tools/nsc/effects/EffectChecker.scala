package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{Transform, TypingTransformers}
import plugins.PluginComponent
import collection.{mutable => m}

abstract class EffectChecker[L <: CompleteLattice] extends PluginComponent with Transform with TypingTransformers {
  // abstract val global: Global
  import global._
  import analyzer.Typer

  // abstract runsAfter: List[String]
  // abstract phaseName: String



  /*********
   * STATE
   ********/

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
  val rhsEffect: m.Map[Symbol, Elem] = new m.HashMap()



  /********************
   * ABSTRACT MEMBERS
   *******************/

  val lattice: L
  type Elem = lattice.Elem

  /**
   * Wee need to know which annotations denote the effects of this system.
   * The inference algorithm needs to be able to remove intermediate
   * effect annotations, it removes annotations that have a type symbol
   * found in this list.
   */
  val annotationClasses: List[Symbol]


  /***************
   * ANNOTATIONS
   **************/


  /**
   * @TODO: treat `@pure` here, i.e. let every subclass decide how to handle it?
   * or assign `lattice.bottom` directly in the EffectInferencer?
   */
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem]
  def fromAnnotation(tpe: Type): Option[Elem] = fromAnnotation(tpe.finalResultType.annotations)

  def toAnnotation(elem: Elem): AnnotationInfo



  val inferAnnotation  = definitions.getClass("scala.annotation.effects.infer")
  val refineAnnotation = definitions.getClass("scala.annotation.effects.refine")
  val pureAnnotation   = definitions.getClass("scala.annotation.effects.pure")



//  def newPhase(prev: Phase): Phase = new StdPhase(prev) {
//    def apply(unit: CompilationUnit) {
//      EffectChecker.this.unit = unit
//      checker.transformUnit(unit)
//      EffectChecker.this.unit = null
//    }
//  }


  /***********
   * HELPERS
   **********/

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


  def typeWithResult(tp: Type, res: Type): Type = {
    onResultType(tp, oldRes => {
      assert(res <:< oldRes, "effect-refined type does not conform: "+ res +" <:< "+ oldRes)
      removeAnnotations(res, annotationClasses).withAnnotations(oldRes.annotations)
    })
  }

  /**
   * Updates the result type of `sym` to `newRt`, but keeps the
   * annotations of the current result type.
   */
  def updateResultType(sym: Symbol, newRt: Type) {
    sym.updateInfo(typeWithResult(sym.tpe, newRt))
  }

  def addFunctionRefinement(funTp: Type, effect: Elem, owner: Symbol, pos: Position): Type = {
    import definitions.FunctionClass
    (funTp: @unchecked) match {
      case TypeRef(pre, sym, refArgs) if sym == FunctionClass(refArgs.length - 1) =>
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

      case RefinedType(parents, decls) =>
        val method = decls.lookup(nme.apply)
        assert(method != NoSymbol, "unexpected refinement")
        method.updateInfo(typeWithEffect(method.tpe, effect))
        funTp
    }
  }



  /**************************
   * CHECKER TRANSFORMATION
   *************************/

  /**
   * Checks effect conformance
   *  - Method's effect conforms to effect annotation on return type
   *  - Conformance of refinement types with effect annotations
   */
  class Checker(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case dd @ DefDef(_, _, _, _, _, rhs) if !rhs.isEmpty =>
          val td = super.transform(dd).asInstanceOf[DefDef]
          checkDefDef(td, localTyper, currentOwner, unit)

        case vd @ ValDef(_, _, _, rhs) if !rhs.isEmpty =>
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

    val symEff = fromAnnotation(sym.tpe).getOrElse(abort("no latent effect annotation on "+ sym))
    val symTp = sym.tpe.finalResultType // @TODO: what about type parameters? def f[T](x: T): T = x

    if (!inferEffect.contains(sym)) {
      // Check or infer the latent effect
      val rhsEff = computeEffect(dd.rhs)
      if (!lattice.lte(rhsEff, symEff))
        effectError(dd, symEff, rhsEff)
    }

    val refinedRhs = transformed.getOrElse(sym, {
      if (sym.isConstructor) {
        dd.rhs
      } else {
        // Check or infer the return type
        val rhs1 = refine(dd.rhs, typer, owner, unit)
        checkRefinement(dd, rhs1.tpe, symTp)
        rhs1
      }
    })

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

    val refinedRhs = transformed.getOrElse(sym, {
      val rhs1 = refine(vd.rhs, typer, owner, unit)
      checkRefinement(vd, rhs1.tpe, symTp)
      rhs1
    })

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
     * annotsInferMode enables the AnnotationCheckers for checking
     * refinements, e.g.
     *   tp1 = (Int => Int) { def apply(x: Int): Int @noEff }
     *   tp2 = (Int => Int) { def apply(x: Int): Int @eff }
     *
     * BUT: Types of trees do NOT contain latent effects, e.g.
     *   tp1 = ConstantType(Int(1))
     *   tp2 = Int @noEff
     *
     * => since we enable the AnnotationChecker, we have to remove
     *    the latent effect from `tp2`. Latent effects are checked
     *    seperately.
     */
    val tp2WithoutEffect = onResultType(tp2, rt => removeAnnotations(rt, annotationClasses))
    // @TODO: should only enable annotation checking for current effect system, not for all
    if (!annotsInferMode(tp1 <:< tp2WithoutEffect)) {
      refinementError(tree, tp2, tp1)
    }
  }


  /*************************
   * COMPUTING REFINEMENTS
   ************************/

  def refine(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): Tree = {
    val refiner = new RefineTransformer(unit, typer, owner, tree)
    refiner.refine()
  }

  /**
   * Only works if `sym` is in the map `refineType`, i.e. if the refinement of `sym` is being inferred.
   */
  def refineRhs(sym: Symbol, typer: Typer, owner: Symbol, unit: CompilationUnit): Tree = {
    val rhs = refineType(sym) match {
      case DefDef(_, _, _, _, _, rhs) => rhs
      case ValDef(_, _, _, rhs)       => rhs
    }
    refine(rhs, typer, owner, unit)
  }

  /**
   * Returns the type of the "rhs" of the definition for "sym".
   */
  def computeType(sym: Symbol, origTp: Type, typer: Typer, owner: Symbol, unit: CompilationUnit): Type = {
    // computeType can be called multiple times (value, getter, setter)
    val refined = transformed.getOrElseUpdate(sym, refineRhs(sym, typer, owner, unit))

    val packed = typer.packedType(refined, sym)
    val widened = typer.namer.widenIfNecessary(sym, packed, WildcardType)

    /**
     * Effect annotations on the tree make no sense, need to remove them! Otherwise
     *
     *   def foo(x: Int): Int @infer = x
     *   def bar: Int @refine = foo(1)
     *
     * "bar" will have effect "@eff" (because it's a method) and "@noEff" (because
     * the inferred type of "foo(1)" is "Int @noEff"
     */
    val resTp = removeAnnotations(widened, annotationClasses)

    // @TODO: more systematic way to keep existing effects...
    // maybe the right solution is to store the latent effect annotations in the rhs trees, not only on the result type.

    // LATER: probably not keep latent effect in trees:
    //   - deleting and re-typing will remove that information
    //   - it heavily conflicts with the way TypeConstraints work! if we select a Symbol with @noEff, the latent
    //     effect can still be @eff. But the typer will assing a type with @noEff


    onResultType(origTp, tp => resTp.withAnnotations(tp.annotations))
  }



  // @TODO: maybe have anoter parameter "pt", which will be used for re-type-to
  class RefineTransformer(unit: CompilationUnit, typer: Typer, owner: Symbol, tree: Tree) extends TypingTransformer(unit) {
    localTyper = typer
    currentOwner = owner

    var result = tree

    def refine(): Tree = {
      transform(result)
      localTyper.typed(result)
    }

    protected def untypeTo(stop: Tree, untypeStop: Boolean = false) {
      // transformer because it might remove some "TypeApply" nodes
      result = new ResetTransformer(stop, untypeStop).transform(result)
    }

    protected def untypeIfRefined(tree: Tree): Tree = {
      if (refineType.contains(tree.symbol)) {
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
        val refinedBody = EffectChecker.this.refine(body, localTyper, owner, unit)
        val restpe = localTyper.packedType(refinedBody, tree.symbol).deconst
        val funtpe =
          if (restpe == tree.tpe) tree.tpe
          else tree.tpe match {
            case TypeRef(pre, sym, args) => typeRef(pre, sym, args.dropRight(1) :+ restpe)
            case RefinedType(parents, decls) => abort("todo: handle multiple refinements of functions")
          }

        val eff = computeEffect(refinedBody)
        val refinedType = addFunctionRefinement(funtpe, eff, currentClass, tree.pos)
        if (refinedType != funtpe) {
          tree.tpe = refinedType
          untypeTo(tree)
        }

        treeCopy.Function(tree, params, refinedBody)

      case Select(qual, name) =>
        // @TODO: maybe untype qualifier?
        untypeIfRefined(tree)

      case Ident(name) =>
        untypeIfRefined(tree)

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
          case tt @ TypeTree() =>
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




  /*********************
   * COMPUTING EFFECTS
   ********************/

  def computeEffect(sym: Symbol): Elem = {
    computeEffect(inferEffect(sym).rhs)
  }

  /**
   * Compute and return the effect caused by executing `tree`
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

    override def traverse(tree: Tree) {
      tree match {
        case ClassDef(_, _, _, _)                     => ()
        case ModuleDef(_, _, _)                       => ()
        case DefDef(_, _, _, _, _, _)                 => ()
        case ValDef(_, _, _, _) if tree.symbol.isLazy => ()
        case Function(_, _)                           => ()

        /** @TODO on Select and Ident
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
      val sym = fun.symbol
      val eff = fromAnnotation(sym.tpe) // will complete lazy type if necessary
      println("effect of applying "+ sym +": "+ eff)
      eff.getOrElse(lattice.top) // @TODO: top by default?
    }
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


  /***************
   * INTEGRATION
   **************/


  def newTransformer(unit: CompilationUnit) = {
    this.unit = unit
    new Checker(unit)
  }

  /**
   * Add an AnnotationChecker to influence `lub` and `glb` computations
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
   * Useful for error reporting
   */
  var unit: CompilationUnit = _

  /**
   * This method is called when the actual effect of a method does not conform
   * to the annotated one.
   */
  def effectError(tree: Tree, expected: Elem, found: Elem) {
    unit.error(tree.pos, "effect mismatch;\n found   : "+ found +"\n required: "+ expected)
  }

  /**
   * This method is called when an overriding method has a larger
   * effect than the overridden one.
   */
  def overrideError(tree: Tree, overridden: Symbol, expected: Elem, found: Elem) {
    effectError(tree, expected, found)
  }

  def refinementError(tree: Tree, expected: Type, found: Type) {
    unit.error(tree.pos, "effect type mismatch;\n found   : "+ found +"\n required: "+ expected)
  }

}
