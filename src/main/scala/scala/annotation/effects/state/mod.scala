package scala.annotation.effects
package state

/**
 * An effect `@mod(x)` denotes modification of the locality
 * of x, where x has to be a parameter (or this).
 * Purity is expressed as `@mod()`.
 */
class mod(locations: Any*) extends Effect

/**
 * The `@modIfLoc` effect expresses modification effect under
 * the condition that a certain parameter is local. For example:
 *
 * def setX(a: A, c: C): Unit @modIfLoc(a, c) = {
 *   a.x = c
 * }
 *
 * Invocations to `setX` have effect `@mod(a)`, but only if the
 * value `c` is fresh or has locality `@loc(a)`, otherwise the
 * invocation has the global effect `@modAll`.
 *
 * val c = new C   // @loc(), i.e. fresh
 * setX(someA, c)  // @mod(someA), since `c` is fresh
 */
class modIfLoc(location: Any, param: Any) extends Effect

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
 *
 * @TODO: is @loc an effect? defenitely not in the sense that "effects
 *   accumulate on the call graph". it's more like a regular type. use
 *   a pluggable type system?
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
