package scala.annotation.effects
package state

case object any
case object fresh

/**
 * An effect `@mod(l)` denotes the effect of modifying the location l.
 * It is equivalent to having `@store(l, fresh)`.
 * 
 * Modifying multiple locations `@mod(l, m)` is equivalent to having two
 * annotations `@mod(l) @mod(m)`.
 * 
 * Purity is denoted as `@mod(fresh)` or equivalently `@mod()`.
 * The largest possible effect is denoted as `@mod(any)`.
 */
class mod(lcos: Any*) extends Effect

/**
 * The `@store` annotation expresses the effect of storing
 * a locality into another one.
 *
 *   // assume the field c is @local in a.
 *   def setC(a: A, c: C): Unit @store(a, c) = { a.c = c }
 *
 * If the argument for `c` is a fresh value, an invocation of
 * `setC` has effect `@mod(a)`. Example:
 *
 *   val c = new C   // @loc(), i.e. fresh
 *   setC(someA, c)  // @mod(someA), since `c` is fresh
 *
 * If the locality of `c` is `any`, then the effect of invoking
 * `setC` is the topmost effect, `@mod(any)`.
 * 
 * There are certain equivalences between `@mod` and `@store` effects:
 *  - @mod() == @mod(fresh) == @store(fresh) == @store(fresh, fresh)  (1)
 *  - store in fresh location: @store(fresh, l)                       (2)
 *  - storing fresh values: @mod(a) == @store(a) = @store(a, fresh)   (3)
 *  - largest effect: @mod(any) == @store(any, l) == @store(l, any)   (4)
 *
 * (1): modifying fresh objets has a non-observable effect. storing a
 *      location into a fresh object changes the location of the fresh
 *      object, but does not have itself an observable effect.
 * (2): when storing inside a fesh object, the locality of that object
 *      changes to the locality of the argument `l`. For example:
 *       def foo(c: C): A @loc(c) = { new A().setC(c) }
 * (3): storing fresh objects in a locality is allowed, the effect is
 *      modifying that locality. The locality of the fresh stored changes.
 * (4): storing an unknown (any) value in some location can create arbitrary
 *      aliases, so this is equivalent to the largest effect
 */
class store(in: Any, from: Any*) extends Effect

/**
 * Denotes the side-effect of assigning to a local variable.
 *
 * def f: C @loc(this) = {
 *   var c = someGlobalC
 *   def g(): Unit @assignStrong(c, this) { c = this.c }
 *   g()
 *   c
 * }
 *
 * The annotation can only occur on nested methods, top-level methods
 * cannot re-assign any outer variables: assigning a field (o.f = x)
 * has effect @mod(o) (or, @store(o, x)).
 *
 * Purity:                   @assign(fresh)
 * Unknown target:           @assign(l, any)
 * Assign any variable to l: @assign(any, l)
 * Largest effect:           @assign(any, any)
 *
 * A weak assignment is one that might or might not happen, depending
 * on the control flow of the method.
 */
class assign(to: Any, from: Any*) extends Effect
class assignStrong(to: Any, from: Any*) extends Effect

/**
 * The effect `@loc(l)` denotes the locality of the returned value.
 * For instance, getter methods of `@local` fields have locality
 * `@loc(this)`.
 *
 * Methods returning a freshly allocated value have the effect
 * `@loc()`, which is equivalent to `@loc(fresh)`.
 */
class loc(locs: Any*) extends Effect



/**
 * Fields whose content is part of the locality of an object have
 * to be marked with `@local`.
 */
class local extends scala.annotation.StaticAnnotation // this is not an effect

