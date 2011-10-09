package scala.annotation
package effects

/**
 * Mark the effect of a method as pure.
 *
 * The anotations here are not effects, not TypeConstraints,
 * they are just markers in the source code.
 *
 * Example why `pure` extends `Effect` (not just `Annotation`): in
 * the collections, we have
 * 
 *   val empty = new Itor[Nothing] {
 *     def next(): Nothing @pure = ...
 *   }
 * 
 * The compiler infers as type of the field (an the getter)
 * 
 *   Itor[Nothing] { def next(): Nothing @pure }
 * 
 * even if the `pure` annotation is not a TypeConstraint. But in the
 * implementation of the getter, which simply selects the field `empty`,
 * the compiler computes type
 * 
 *   Itor[Nothing] { def next(): Nothing }
 * 
 * For the selection. This will result in an (effect-) subtyping error.
 * Therefore, the `pure` annotation needs to be a type constraint (or
 * extend `Effect`).
 * 
 * @TODO: check what happens if `infer` or `refine` appear in such a
 * position in the soure.
 */
class pure extends Effect

/**
 * Mark the effect of a method for being inferred.
 */
class infer extends Annotation

/**
 * Mark the type of a (return) type of a field / method to be
 * refined with effect annotations.
 */
class refine extends Annotation
