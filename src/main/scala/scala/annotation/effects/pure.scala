package scala.annotation
package effects

/**
 * Mark the effect of a method as pure.
 *
 * The anotations here are not effects, not TypeConstraints,
 * they are just markers in the source code.
 *
 * @TODO: maybe `pure` should extend `Effect`, to be seen.
 */
class pure extends Annotation

/**
 * Mark the effect of a method for being inferred.
 */
class infer extends Annotation

/**
 * Mark the type of a (return) type of a field / method to be
 * refined with effect annotations.
 */
class refine extends Annotation
