package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{InfoTransform, TypingTransformers}
import plugins.PluginComponent

abstract class EffectInferencer[L <: CompleteLattice] extends PluginComponent with InfoTransform with TypingTransformers {

  val checker: EffectChecker[L]
  import checker._
//  protected type Elem = checker.Elem

  val global: checker.global.type = checker.global
  import global._

  /**
   * The EffectInferencer has to be a dummy InfoTransformer. This is to invalidate
   * caches of symbol types, because types can change. Example:
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
   * the EffectInferencer an InfoTransform, not the EffectChecker.
   */
  def transformInfo(sym: Symbol, tp: Type): Type = tp

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
      tree match {
          /*
        case DefDef(_, _, _, _, _, _) if sym.isGetter =>
          updateEffect(sym, getterEffect(sym))

        case DefDef(_, _, _, _, _, _) if sym.isSetter =>
          updateEffect(sym, setterEffect(sym))
*/
        case DefDef(_, _, _, _, _, _) if (sym.isGetter || sym.isSetter) =>
          ()

        case dd @ DefDef(_, _, tparams, vparamss, tt @ TypeTree(), rhs) =>
          val (transOwner, transTyper) = atOwner(tree.symbol)((currentOwner, localTyper))

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
            checker.inferEffect += sym
          else if (hasNoE)
            updateEffect(sym, lattice.top)

          if (inferT)
            refineType += sym

          val tp = sym.tpe // updateEffect called above changes this type (adds an effect)!
          if (inferE || inferT)
            // updateInfo to lazy type is not allowed
            sym.setInfo(mkLazyType(sym => {
              transTyper.reenterTypeParams(tparams)
              transTyper.reenterValueParams(vparamss)
              
              val refinedType =
                if (inferT) computeType(sym, rhs, tp, transTyper, transOwner, unit)
                else tp

              val annotType =
                if (inferE) typeWithEffect(refinedType, computeEffect(sym, rhs, transTyper, transOwner, unit))
                else refinedType

              // setInfo so that the lazy type doesn't remain in type history. otherwise
              // it can be called again in a later run, which is problematic / wrong.
              sym.setInfo(annotType)
            }))

        case vd @ ValDef(_, _, tt @ TypeTree(), rhs) =>
          val (transOwner, transTyper) = atOwner(tree.symbol)((currentOwner, localTyper))

          if (rhs.isEmpty || !inferRefinement(sym, tt.wasEmpty)) {
            val getter = sym.getter(sym.owner)
            if (getter != NoSymbol)
              updateEffect(getter, getterEffect(getter))
            val setter = sym.setter(sym.owner)
            if (setter != NoSymbol)
              updateEffect(setter, setterEffect(setter))
          } else {
            val tp = sym.tpe
            refineType += sym

            sym.setInfo(mkLazyType(_ => {
              sym.setInfo(computeType(sym, rhs, tp, transTyper, transOwner, unit))
            }))

            val getter = sym.getter(sym.owner)
            if (getter != NoSymbol)
              getter.setInfo(mkLazyType(_ => {
                val refinedType = computeType(sym, rhs, tp, transTyper, transOwner, unit)
                val getterType = typeWithEffect(NullaryMethodType(refinedType), getterEffect(getter))
                getter.setInfo(getterType)
              }))

            val setter = sym.setter(sym.owner)
            if (setter != NoSymbol)
              setter.setInfo(mkLazyType(_ => {
                val arg = setter.newSyntheticValueParam(computeType(sym, rhs, tp, transTyper, transOwner, unit))
                val setterType = typeWithEffect(MethodType(List(arg), definitions.UnitClass.tpe), setterEffect(setter))
                setter.setInfo(setterType)
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
      // run in next phase, so that caches are invalidated, see comment on transformInfo.
      atPhase(phase.next)(c(s))
    }
  }
}
