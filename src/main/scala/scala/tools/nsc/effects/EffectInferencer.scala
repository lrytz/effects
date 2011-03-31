package scala.tools.nsc.effects

import scala.tools.nsc._
import transform.{InfoTransform, TypingTransformers}
import plugins.PluginComponent

abstract class EffectInferencer[L <: CompleteLattice] extends PluginComponent with InfoTransform with TypingTransformers {

  val checker: EffectChecker[L]
  import checker._

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
   * Works similar to the Namer phase of the compiler.
   */
  def newTransformer(unit: CompilationUnit) = new TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      val sym = tree.symbol

      tree match {
        case DefDef(_, _, _, _, _, _) if (sym.isGetter || sym.isSetter) =>
          () // they are handled in `case ValDef`

        case dd @ DefDef(_, _, tparams, vparamss, tt @ TypeTree(), rhs) =>
          val (transOwner, transTyper) = atOwner(tree.symbol)((currentOwner, localTyper))
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

        case vd @ ValDef(_, _, tt @ TypeTree(), rhs) =>
          val (transOwner, transTyper) = atOwner(tree.symbol)((currentOwner, localTyper))

          // at typer phase so that lazy effect types get forced yet.
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
