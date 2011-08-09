package scala.annotation
package effects

/**
 * @TODO: do effects need to be TypeConstraints? If we say that effect
 * annotations only make sense on return types, not anywhere else, then
 * this is a bit problematic:
 *
 *   def floo(): Int @eff = { ... }
 *   val x = floo()
 *
 * Because `eff` is a TypeConstraint, `x` gets the type `Int @eff`, which
 * would be nonsense.
 *
 * However, maybe we'll change things and decide to actually annotated
 * latent effects in trees, so that the expression `floo()` should have
 * type `Int @eff`. In some sense, this would be more systematic: in a
 * DefDef, the type of the method (e.g. `(Int)Int @eff`) would match the
 * type of the rhs (`Int @eff`).
 *
 * ---------------------------------------------------------
 * LATER: probably not keep latent effect in trees:
 *   - deleting and re-typing will remove that information
 *   - it heavily conflicts with the way TypeConstraints work! if we select a Symbol with @noEff, the latent
 *     effect can still be @eff (because of the effect of the qualifier). But the typer will assing a type with @noEff
 * ---------------------------------------------------------
 *
 * Another problem: given "class C { def f: Int @noEff = 1 }". In
 *   def foo = getC().f
 * the type checker will infer type "Int @noEff" for "foo", but that
 * is wrong, "getC()" can have effects.
 *
 *
 *
 * BUT ACTUALLY: Effects NEED to be TypeConstraints. Otherwise, they get lost
 * in TypeMaps in cases like
 *
 *   object t { val f: (Int => Int) { def apply(x: Int): Int @eff } = { ... } }
 *   val g = t.f
 *
 * Here, the refinement has to be kept. This only works with TypeConstraints.
 *
 * Also, not having them TypeConstraints breaks refinement inference, i.e. in
 * the following, the type of `c` is `C`, not a refinement:
 *
 *   def c: C @infer @refine = new C { def f: Int @infer = 1 }
 * 
 * 
 * 
 * SO: we have a conflict of interests here.. They need to be TypeConstraints for some
 * functionality, but making them TypeConstraints messes up with things.. So we basically
 * want to remove all effect annotations that the (normal) type checker adds to return types
 * of methods (and also fields, which of course can't have an effect anyway). This might be
 * non-trivial in some cases. Example:
 * 
 *   abstract class A { def mod(): Unit @mod(this) }
 *   def foo(a: A) = { val x = a; x.mod() }
 * 
 * The compiler infers for method `foo` the type `Unit @mod(x) forSome { val x: A }` !!!
 * I.e. a MethodType whose result type is an ExistentialType
 * 
 * Solution:
 *  - traversal to remove all typer-inferred effect annotations
 *  - special-case the type-checker to know about the `Effect` class, just as it knows about
 *    `TypeConstraint`, and change how inference works.
 *  - drop the annotations that were inferred by the typer "along the way", in the EffectInferencer
 *    (current "solution", but breaks on these existential types)
 *    
 * PROBLEM with current solution: if an effect system is not enabled, but annotations are there,
 * the will infer wrong effect annotations which are not deleted and end up being pickled.
 */
trait Effect extends StaticAnnotation with TypeConstraint
