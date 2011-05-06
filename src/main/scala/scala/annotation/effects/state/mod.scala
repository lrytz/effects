package scala.annotation.effects
package state


/**
 * An effect `@mod(x)` denotes modification of the locality
 * of x, where x has to be a parameter (or this).
 * Purity is expressed as `@mod()`.
 */
class mod(locations: Any*) extends Effect

/**
 * The effect `@modAll` denotes arbitrary state modifications,
 * including modifications to global state.
 */
class modAll extends Effect


/**
 * The effect `@fresh` is an alias for `@loc()`, meaning that
 * the returned object is not in the locality of any other
 * existing value.
 */
//class fresh extends Effect

/**
 * The effect `@loc(x)` denotes the locality of the returned value.
 * For instance, getter methods of `@local` fields have locality
 * `@loc(this)`.
 *
 * Freshly allocated values have the effect `@loc()`.
 */
class loc(locations: Any*) extends Effect

/**
 * The effect `@nonLoc` denotes unknown locality
 */
class nonLoc extends Effect


/**
 * Fields whose content is part of the locality of an object have
 * to be marked with `@local`.
 */
class local extends scala.annotation.StaticAnnotation // this is not an effect
