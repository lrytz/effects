package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{InfoTransform, TypingTransformers}
import plugins.PluginComponent


/**
 * Effect checking and inference works very similar to type checking and inference. For
 * each effect system, there are two phases added to the compilation: an EffectInferencer
 * and an EffectChecker. These pairs behave very similarly to the Namer-Typer phase during
 * ordianry type-checking.
 * 
 * The EffectInferencer is a transformer phase, but it does not actually change the trees
 * in any way (see `def transform`: it calls `super.transform` in the end). However, it still
 * needs to be a transformer, because the it needs a local typer instance which has the right
 * context in each DefDef or ValDef, which is provided by TypingTransformer. Therefore, the
 * EffectInferencer is implemented using a TypingTransformer (if a TypingTraverser existed,
 * that could e used).
 * 
 * What the effectInferencer does is assigning lazy types to some method and value symbols.
 * There are two situations in which the type of a symbol changes:
 * 
 *  1. Effect inference, the type of a method acquires an effect annotation. Example:
 *  
 *       def foo(): Int @infer = { do-stuff(); 1 }
 *
 *     The type of foo will be a lazy type that, when completed, computes the effect of the
 *     body using `computeEffect`, and then assigns the type `Int @someEffect` to the symbol
 *     of `foo`.
 *     
 *  2. Refinement type inference, the type of the returned value becomes a refinedment. This
 *     mostly happens with anonymous functions, for example:
 *     
 *       val f: (Int => Int) @refine = (x: Int) => x + 1
 *       val g: C @refine = new C { def foo() = 1 }
 *     
 *     The EffectInferencer assigns a lazy type that, when being completed, computes the type
 *     of the righthand side using `computeType`. In both examples, the type of the expression
 *     becomes more specific when taking side effects into account. Concretely they are:
 *     
 *       f: (Int => Int) { def apply(x: Int): Int @pure }  // i.e. a pure Function
 *       g: C { def foo(): Int @pure }                     // i.e. a `C`, but with a pure `foo`
 *
 *
 * The code that computes side-effects (`computeEffect`) and refined types (`computeType`) is
 * in the EffectChecker class, see there for more documentation.
 * 
 * 
 * === TYPING TRANSFORMERS ===
 * 
 * There are three typing transformers involved in the effect checking process
 * 
 *  - EffectInferencer is a TypingTransformer (see explanation above)
 *  - RefineTransformer (in the EffectChecker), see its documentation
 *  - Checker (in EffectChecker), see its documentation
 * 
 * The defining property of a TypingTransformer is that while traversing a tree, it always
 * provides a typer instance (`localTyper`) with the right context for the current subtree,
 * and the `currentOwner` symbol.
 * This is done using the `atOwner(sym)(body)` function, which the traverser invokes on every
 * tree that defines a symbol (ClassDef, DefDef etc).
 * 
 * One problem is that the RefineTransformer is being invoked not on the root of the tree,
 * but basically on the `rhs` tree of a ValDef or DefDef. Therefore, we have to manually
 * initialize its context, which is `localTyper` and `currentOwner`.
 *
 * For that reason:
 *  - Many functions in the EffectChecker (`computeType`, `computeEffect`, `checkDefDef`, ...)
 *    take two arguments `typer` and `owner`, which they basically thread through. Each of
 *    these functions might eventually call `refine`, which creates a RefineTransformer with
 *    the correct context.
 *    
 *  - Since we use the above-mentioned functions in the EffectInferencer and in the Checker
 *    (the two Traversers that start at the root), we need to have the right context at hand.
 *    Therefore, these two are TypingTransformers.
 * 
 * 
 * IMPORTANT NOTE: When modifying these traversers, be careful to keep `currentOwner` and
 * `localTyper` correct, and to use the correct values when calling `refine`, `computeType`
 * or similar. Concretely: The `transform` method in the Transformer calls `atOwner` on
 * every tree that defines a symbol (ClassDef, DefDef, Function, etc), see method `transform`
 * in class `Transformer`.
 * So when you override `transform` and catch such a tree, remember that you have to call
 * `atOwner` yourself in order to get the correct typer!
 *   
 *   MyTypingTransformer <: TypingTransformer {
 *     override def transform(t: Tree) = t match {
 *       case DefDef =>
 *         // currentOwner, localTyper still refer to the outer next
 *         atOwner(t.symbol) {
 *           // here, you have the currentOwner, localTyper for that DefDef
 *         }
 *     }
 *   }
 * 
 * When you call `computeType(rhs, owner, typer)` for instance, you have to pass it the
 * correct owner and typer, i.e. the ones *after* a call to `atOwner`.
 */
abstract class EffectInferencer[L <: CompleteLattice] extends PluginComponent with InfoTransform with TypingTransformers {

  val checker: EffectChecker[L]
  import checker._

  val global: checker.global.type = checker.global
  import global._

  /**
   * The EffectInferencer has to be a dummy InfoTransformer. This is to invalidate
   * caches of symbol-attached types, because types can change. Example:
   *
   *   val f7: (Int => Int) @refine = (x: Int) => x    // (1)
   *   def v7(x: Int): Int @noEff = f7.apply(x)        // (2)
   *
   * The type of "val f7" (1) changes to a "RefinedType".
   *
   * When re-typechecking Select(this.f7, apply) of (2), the type of "this.f7"
   * is "SingleType(this, f7)".
   *
   * typedSelect calls "memberType" on this SingleType, which calls "underlying",
   * which has a cache.
   * The "underlying" of f7 is now different, it used to be "Int => Int", now it's
   * the "RefinedType(Int => Int, {def apply})".
   *
   * If there's no InfoTransform, the cache is not invalidated!
   *
   * Since InfoTransformers are only applied at the next phase, we need to make
   * the EffectInferencer an InfoTransform, not the EffectChecker (where we actually
   * look at the symbol's tyeps).
   */
  def transformInfo(sym: Symbol, tp: Type): Type = tp

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

  // documented above, on class EffectInferencer
  def newTransformer(unit: CompilationUnit) = new TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      val sym = tree.symbol

      tree match {
        case DefDef(_, _, _, _, _, _) if (sym.isGetter || sym.isSetter) =>
          () // they are handled in `case ValDef`

        case DefDef(_, _, tparams, vparamss, tt @ TypeTree(), rhs) =>
          /* See documentation on class EffectInferencer.
           *  - `transOwner` is the method symbol
           *  - `transTyper` is the typer for the method body
           */
          val (transOwner, transTyper) = atOwner(tree.symbol)((currentOwner, localTyper))
          
          // A typer on a DefDef is only works correctly after entering the parameters.
          // The same is done in `typedDefDef` in the typer.
          transTyper.reenterTypeParams(tparams)
          transTyper.reenterValueParams(vparamss)

          /**
           * If "tt" was inferred there might be a wrong effect annotation.
           *   class C { def f: Int @noEff }
           *   def m = getC().f
           * Typer infers type `Int @noEff` for m, which is wrong.
           * 
           * @TODO: is `wasEmpty` always correct?
           */
          val hasNoE = tt.wasEmpty || fromAnnotation(sym.tpe).isEmpty
          val inferE = hasNoE && inferEffect(sym) && (!sym.isConstructor || inferConstructorEffect(sym))
          val inferT = !rhs.isEmpty && inferRefinement(sym, tt.wasEmpty)

          if (inferE)
            checker.inferEffect += sym
          else if (hasNoE)
            updateEffect(sym, lattice.top)

          if (inferT)
            refineType += sym

          val tp = sym.tpe // don't move this valdef before the `updateEffect` above!
          if (inferE || inferT)
            sym.updateInfo(mkLazyType(sym => {

              val refinedType =
                if (inferT) computeType(sym, rhs, tp, transTyper, transOwner, unit)
                else tp

              val annotType =
                if (inferE) typeWithEffect(refinedType, computeEffect(sym, rhs, transTyper, transOwner, unit))
                else refinedType

              // updateInfo removes the lazy type from the type history
              sym.updateInfo(annotType)
            }))

        case ValDef(_, _, tt @ TypeTree(), rhs) =>
          val (transOwner, transTyper) = atOwner(tree.symbol)((currentOwner, localTyper))

          // at typer phase so that lazy effect types don't get forced yet.
          val (getter, setter) = atPhase(currentRun.typerPhase)(sym.getter(sym.owner), sym.setter(sym.owner))

          if (rhs.isEmpty || !inferRefinement(sym, tt.wasEmpty)) {
            if (getter != NoSymbol)
              updateEffect(getter, getterEffect(getter))
            if (setter != NoSymbol)
              updateEffect(setter, setterEffect(setter))
          } else {
            refineType += sym

            val fieldTpe = sym.tpe
            sym.updateInfo(mkLazyType(_ => {
              sym.updateInfo(computeType(sym, rhs, fieldTpe, transTyper, transOwner, unit))
            }))

            if (getter != NoSymbol) {
              val getterTpe = getter.tpe
              getter.updateInfo(mkLazyType(_ => {
                val refinedType = computeType(sym, rhs, getterTpe, transTyper, transOwner, unit)
                val getterType = typeWithEffect(refinedType, getterEffect(getter))
                getter.updateInfo(getterType)
              }))
            }
            
            if (setter != NoSymbol) {
              val setterTpe = setter.tpe
              setter.updateInfo(mkLazyType(_ => {
                val MethodType(List(arg), res) = setterTpe
                val newArg = setter.newSyntheticValueParam(computeType(sym, rhs, arg.tpe, transTyper, transOwner, unit))
                val setterType = typeWithEffect(MethodType(List(newArg), res), setterEffect(setter))
                setter.updateInfo(setterType)
              }))
            }
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
      // run in next phase, so that caches are invalidated, see comment on transformInfo.
      atPhase(phase.next)(c(s))
    }
  }
}
