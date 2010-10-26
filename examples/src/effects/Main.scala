package effects


// effect annotations
trait Effect extends TypeConstraint

// masking only on effect params and param calls!
// class mask(effects: Effect*) extends TypeConstraint

case class ep(name: Symbol /*, bounds: Effect* */) extends Effect

// @TODO: is `pc` really a TypeConstraint? Look at the forwarding example, there it isn't really.
// but otherwise, effects have to be TypeConstraints, this will make the applyFirst example work.
case class pc(call: Any, mask: Seq[Effect] = Nil, propagate: Seq[Effect] = Nil) extends Effect
case class pcs(calls: Any*) extends Effect

// this means pure for all domains. pure inside domains can
// be done individually (e.g. @throws[Nothing] for exceptions)
class pure extends Effect
object pure extends Effect


// concrete effects
trait |[E1 <: Throwable, E2 <: Throwable] extends Throwable
class throws[E <: Throwable] extends Effect
object throws { def apply[E <: Throwable] = new throws[E] }



object Main {
  // some exceptions
  class E1 extends Exception
  class E2 extends Exception
  class E3 extends Exception


  // some classes
  class A {
    def f: B = new B
  }
  class B {
    def g: String @throws[E1 | E2] = "foo"
  }
  class A1 extends A {
    override def f: B1 = new B1
  }
  class B1 extends B {
    override def g: String @throws[E1] = "bar"
  }



  // effectful method

  def foo: Unit @throws[E2] = {
    throw new E2
  }




  // polymorphism on second level

  def ab(a: A): String @pc(a.f.g) = {
    a.f.g
  }

  ab(new A1): @throws[E1]



  // polymorphism, dependencies

  def app(a: A, f: A => String): String @pc(f.apply(a)) = f(a)

  app(new A1, ((a: A) => a.f.g): (A => String) { def apply(a: A): String @pc(a.f.g) }): @throws[E1]

  // or:    app(new A1, a => (a.f.g: String @pc(a.f.g))): @throws[E1]

  // later: app(new A1, (a => a.f.g): (a: A => String @pc(a.f.g))): @throws[E1]





  // functional values

  val f: (B => String) { def apply(b: B): String @pc(b.g) } = (b: B) => b.g
  // val f: (b: B) => String @pc(b.g) = (b: B) => b.g



  // forwarding

  def forward1(b1: B): String @pc(b1.g) = forward2(b1)
  def forward2(b2: B): String @pc(b2.g) = b2.g



  // nesting: defs inside defs

  def nestDef(b1: B): String @throws[E1] @pc(b1.g) = {
    def bar(b2: B): String @pcs(b1.g, b2.g) = {
      b1.g + b2.g
    }
    bar(new B1)
  }



  // nesting: functions inside functions (-> currying!)

  val nestFun: (B => (String => String)) { def apply(b: B): ((String => String) { def apply(s: String): String @pc(b.g) }) @throws[E3] } = (b: B) => {
    if (math.random < 0.5) throw new E3
    (s: String) => b.g + s
  }

  val n1: (String => String) { def apply(s: String): String @throws[E1] } = (nestFun(new B1): @throws[E3])
  n1("blabla"): @throws[E1]



  // nesting: functions inside defs, defs inside functions

  def nestDefFun(b1: B): String @pc(b1.g) @throws[E1] = {
    val f: (B => String) { def apply(b2: B): String @pcs(b1.g, b2.g) } = (b2: B) => {
      def foo: String @pc(b2.g) = {
        b2.g
      }
      b1.g + foo
    }
    f(new B1) : @pc(b1.g) @throws[E1]
  }


  // partial application of curried methods
  def curried(a: A)(b: B): String @pc(b.g) = {
    b.g
  }
  // OK because of param forwarding
  val partFun: (B => String) { def apply(b: B): String @pc(b.g) } = (b: B) => curried(new A)(b)
  partFun(new B1): @throws[E1]


  // functions with @pc escaping the scope of the parameter
  def escFun(b: B): String => String @pc(b.g) = (s: String) => s + b.g
  val escFun1: String => String @throws[E1] = escFun(new B1)



  // transitive closure

  class C0 { def baz: String @throws[E1] = "" }
  class C1 { def bar(c: C0): String @pc(c.baz) = c.baz }
  def trans(c: C1): String @pc(c.bar(% : C0)) = c.bar(new C0)

  trans(new C1): @throws[E1]



  // pc with arguments (%, other parameters), overloading

  class Ovrl {
    def foo(a: Object, b: String): String @throws[E1] = ""
    def foo(a: String, b: String): String @throws[E2] = a + b
  }

  /**
   * o.foo(%, %) is allowed, it will select (String, String) since both are applicable
   *
   * to test things, use the object
   *   object t {
   *     def foo(a: => Object, b: Object) = 1
   *     def foo(a: => String, b: String) = 2
   *   }
   *
   * then call
   *   t.foo(%, "")           => 2
   *   t.foo(% : Object, "")  => 1
   */

  def ovr(o: Ovrl): String @pc(o.foo(% : Object, % : String)) = {
    o.foo("fla", "flu")
  }

  // see
  app(new A1, a => a.f.g)
  // for an example where the arguments of a @pc call can refer to params of
  // the method




  // converting to functional values, eta-expansion

  def map[A, B](l: List[A], f: A => B): List[B] @pc(f.apply(%)) = l match {
    case x :: xs => f(x) :: map(xs, f)
    case Nil => Nil
  }






  def mapExt[A, B](l: List[A], f: A => B): List[B] @pc(f.apply(x)) forSome {val x: A} = l match {
    case x :: xs => f.apply(x) :: map(xs, f)
    case Nil => Nil
  }



  mapExt(List(1,2,3), (x => {
    if(math.random < 0.5) throw new E1
    else x + 1
  }):  (Int => Int @throws[E1])): @throws[E1]



/*
  // map of the collection library, with builders.

  trait TravLike[+A, +Repr] {

    def repr: Repr @pure = this.asInstanceOf[Repr]

    // @TODO: maybe we want to allow arbitrary effects, and then the subclasses can be
    // more specific (i.e. List)?
    def foreach[U](f: A => U): Unit @pc(f.apply(a)) forSome {val a: A}

    def map[B, That](f: A => B)(implicit bf: CBF[Repr, B, That]): That @pcs(this.foreach(f), f.apply(a), bf.apply(r)) forSome {val a: A; val r: Repr} = {
      val b = bf(repr) // @pc(bf.apply)
      b.sizeHint(this) // @pure
      // for (x <- this) b += f(x)
      this.foreach(x => b += f(x)) // @pc(f.apply)
      b.result // @pure
    }
  }
  trait CBF[-From, -Elem, +To] {
    def apply(from: From): Bldr[Elem, To] // allow any effect, concrete builder factories will be pure
    def apply(): Bldr[Elem, To]           // same here
  }

  trait Bldr[-Elem, +To] extends Grwbl[Elem] {
    def +=(elem: Elem): this.type  // allow any effect, concrete builders will be pure
    def sizeHint(coll: TravLike[_, _], delta: Int = 0): Unit @pure = {
      ()
    }
    def result(): To // @pure
  }
  trait Grwbl[-A] { }

  // need some concrete implementation, e.g. List, to see the real thing.


  trait LinSqOpt[+A, +Repr <: LinSqOpt[A, Repr]] extends TravLike[A, Repr] {
    def isEmpty: Boolean
    def hd: A
    def tl: Repr

    override def foreach[B](f: A => B) {
      var these = this
      while (!these.isEmpty) {
        f(these.hd)
        these = these.tl
      }
    }
  }

  abstract class Lst[+A] extends LinSqOpt[A, Lst[A]] {
    def Cns[B >: A] (x: B): Lst[B] =
      new Cns(x, this)
  }
  case class Cns[B](hd: B, tl: Lst[B]) extends Lst[B] {
    def isEmpty = false
  }
  case object Nl extends Lst[Nothing] {
    def hd = throw new Error()
    def tl = throw new Error()
    def isEmpty = true
  }







  val c = Cns(1, Nl)
  c.map(x => x + 1)
*/



  // works because the parameter "f" is forwareded directly to map, which has a @pc on its corresponding parameter!!!
  val mapPrims: ((Int => Int) => List[Int]) { def apply(f: Int => Int): List[Int] @pc(f.apply(%)) } = (f: Int => Int) => map(List(1, 3, 5, 7, 11, 13), f)
  mapPrims(x => { if (x > 10) throw new E1 else x + 1 }): @throws[E1]

  // @TODO: the refinement type breaks type inference, also here
  // again, works because of param forwarding, but we have to look at it after eta-expansion (should be fine).
  val mapInts: ((List[Int], Int => Int) => List[Int]) { def apply(l: List[Int], f: Int => Int): List[Int] @pc(f.apply(%)) } = (map _): ((List[Int], Int => Int) => List[Int])


  // @TODO error! cannot convert method with dependent method type to a functional value. to be seen.

//  def dep(a: A, f: A => B): B @pc(f.apply(a)) = f(a)
//  dep _


  /**
   * Effect Parameters and Bounds
   *
   *  - an effect on a method's return type (in a refinement) means a bound
   *
   *  - in general, they can only be attached to method return types using type refinements
   *    => Allow short syntax for functions. A => B @ep('X) @throws[E1] means
   *
   *        (A => B) { def apply(a: A): B @ep('X) @throws[E1] }
   *
   *    which is equivalent to the following, if we support having bounds directly in the @ep
   *        (A => B) { def apply(a: A): B @ep('X, throws[E1])
   *
   *  - effect parameters only have to be used when we want polymorphism over a type which is
   *    not the type of an argument (but a part of it), see applyFirst
   *
   *  - lower bound could be useful in contravariant positions (right?). maybe ignore them for now.
   *    if an effect system NEEDS some effect, it's like it NEEDS a capability, so things
   *    can just be turned around in the system?
   *
   *
   *  - question of domains. does it limit the effect only in one domain? or require others pure?
   */


  // @ep: polymorphic on inner type. can't encode dependency (argument to the apply method is a).

  def applyFirst(a: A, fs: List[A => String @ep('e)]): String @ep('e) = fs match {
    case f :: _ => f(a)
    case _ => ""
  }
  //@TODO: need param type (a: A) because of refinement
  applyFirst(new A1, List((a: A) => (a.f.g: @pc(a.f.g))): List[(A => String) {def apply(a: A): String @pc(a.f.g)}]): @throws[E1 | E2]

  /**
   * ADRIAAN: this could maybe be done (at least internally) using implicits, something similar
   *   to bounds. currently we have
   *     def foo[T](implicit w: Mani[T])
   *  ==> the implicit is bounded by the type parameter.
   *
   *  Similiarly, the implicit below could be bounded by the concrete effect of the apply functions of fs.
   */
//  def applyFirst(a: A, fs: List[A => String @ep(w.eff)])(implicit w: Effect): String @ep(w.eff) = fs match {



  // bounds: examples with exceptions

  def forall[A](l: List[A], p: A => Boolean @pure): Boolean @pure = l match {
    case x :: xs => p(x) && forall(xs, p)
    case Nil => true
  }

  forall(List(1,2,3), (x: Int) => x < 10)
  // should be rejected
  forall(List(1, 2, 3), (x: Int) => {
    if (x > 100) throw new E1
    else x < 10
  })

  def safeExec(b: B, f: B => String @throws[E1]): String @pure = {
    try {
      f(b)
    } catch {
      case e: E1 => "nope"
    }
  }

  safeExec(new B, b => "string!")
  safeExec(new B, b => {
    if (math.random < 0.5) throw new E1
    else "suuuper"
  })
  safeExec(new B, b => b.g) // should be rejected


  def boundExec(b: B, f: B => String @throws[E1]): String @pc(f.apply(%)) = {
    f(b)
  }

  (boundExec(new B, b => { throw new E1 }): @throws[E1]) // OK
  (boundExec(new B, b => "dlkfj"): @pure) // OK
  boundExec(new B, b => { throw new E2 }) // reject




  // bounds on @pc: restrict the interface that's exposed to an argument function.

  class BigClass {
    def f(x: Int): Int @pure = 0
    def g(s: String, bc: BigClass): Int @throws[E1] = 1
    def h(): Unit @throws[E1 | E2] = { println("") }
  }

  def funArg(xs: List[BigClass], trans: (BigClass => Unit) { def apply(bc: BigClass): Unit @pcs(bc.f(%), bc.g(%, %)) }): Unit @pc(trans.apply(%)) = {
    for (x <- xs)                                     // bc.f could be omitted since it's pure ^^^^^^^
      trans(x)
  }

  (funArg(List(new BigClass), (bc: BigClass) => {bc.f(10); ()}: @pc(bc.f(%)) ): @pure)
  (funArg(List(new BigClass), (bc: BigClass) => {bc.g("", null); ()}: @pc(bc.g(%, %))): @throws[E1])
  funArg(List(new BigClass), (bc: BigClass) => bc.h(): @pc(bc.h())) // should be rejected, does not conform to required @pc!



  // equivalent argument type:  List[B => String @ep('eff, throws[E1])]
  def boundApplyFirst(b: B, fs: List[B => String @ep('eff) @throws[E1]]): String @ep('eff) = fs match {
    case f :: _ => f(b)
    case _ => ""
  }

  boundApplyFirst(new B, List((b: B) => b.g)) // should be rejected


  /**
   *  EFFECT MASKING
   *
   * Masking makes only sense in the polymorphic case, i.e. we want to express things like
   *  - @pc(f.apply, masking(throws[E1])
   *  - @ep('X, masking(throws[E2])
   *
   *
   * Polymorphism over masking
   *  - can an argument function mask something? Probably not, how should they? One needs to
   *    use the specific masking operation inside the body, calling an argument function does
   *    not mask effects
   *
   *  - an effect as argument to a @pc or @ep means that this effect is forwarded (not masked). Examples:
   *    > @pc(f.apply, mask(throws[E1, E2]))          ==> mask E1 & E2, forward others
   *    > @pc(f.apply, mask(throws[Any]))             ==> mask all exceptions
   *    > @pc(f.apply, mask(throws[Any]), throws[E1]) ==> forward E1, mask all others
   *
   *  - BUT the effect of an argument function can influence the masking, e.g. in
   *
   *      (f: PartialFunction[Throwable, B] @definedAt[E1 | E2] @throws[E3])
   *
   *    we can use f to handle exceptions
   *
   *
   * Extensible masking
   *  - It should be possible to define masking operations for plugin designers! Ideally,
   *    these operations (methdos?) would not even need to be blamed by the plugin but could
   *    just be created by using the right annotations.
   *
   */



  // does not make any sense. we know the effect of foo and what is masked ==> we can as well
  // write down the effect of safeFoo. it could make sense if we consider @pc(this.foo), but
  // since "this" is an object, foo can never be overridden.
  def safeFoo: Unit /* @mask(throws[E2]) */ = try {
    foo
  } catch {
    case e: E2 => ()
  }



  // masking on effect-polymorphic methods
  def mask1(b: B): String @pc(b.g, mask = throws[E1]) = try {
    b.g
  } catch {
    case e: E1 => "got e1"
  }

  (mask1(new B): @throws[E2])
  mask1(new B1): @pure


  def mask2(b1: B, b2: B): String @pc(b1.g, mask = throws[E1]) @pc(b2.g, mask = throws[E1 | E2]) = {
    val s1 = try {
      b1.g
    } catch {
      case e: E1 => "got e1"
    }

    s1 + (try {
      b2.g
    } catch {
      case e: E1 => "again e1"
      case e: E2 => "e2"
    })
  }

  mask2(new B1, new B): @pure




  def mask3(f: Int => String): String @pc(f.apply(%), mask = throws[Throwable]) @throws[E2] = try {
    f(10)
  } catch {
    case e: E2 => throw e
    case e => "got some exception"
  }

  // @TODO: this should be @pure, but it can't.. we don't see in the signature that
  // E2 can only be thrown by the param call "b.g".
  mask3((x: Int) => { throw new E1; "dlkfj" })



  // ==> Anchored exceptions have the concept of "propagating"
  def mask4(b: B): String @pc(b.g, mask = throws[Throwable], propagate = throws[E2]) = try {
    b.g
  } catch {
    case e: E2 => throw e
    case e => "got some other exception"
  }


  mask4(new B1): @pure




  // however, this is probably not useful in so many situations. example:
  def mask5(b: B): String @pc(b.g, mask = throws[Throwable]) @throws[E2] = try {
    b.g
    if (math.random < 0.5) throw new E2
    else "oof rab"
  } catch {
    case e: E2 => throw e
    case e => "boo far"
  }

  mask5(new B1)





  // multiple param calls inside one try: mask on both

  def mask5(b1: B, b2: B): String @pc(b1.g, mask = throws[E1]) @pc(b2.g, mask = throws[E1]) = try {
    b1.g + b2.g
  } catch {
    case e: E1 => "fuubar"
  }

  

  /**
   * Masking exceptions: we need more information. The effect of the try-catch block depends
   * on the partial function given as argument, namely on what types it is defined on.
   *
   * So we could add another type and effect system tracking the types on which a partial
   * function is defined
   *
   * TODO: this is in fact not so much an effect system, but rather a classical "pluggable
   * type system". question: are the two the same? can they be unified? or, more likely: can
   * our effect system express arbitrary pluggable type systemsm?
   *
   */

  class definedAt[E <: Throwable] extends Effect
  object caughtBy {
    def apply[T](pf: PartialFunction[Throwable, T]) = new Effect {}
  }

  val pf1: PartialFunction[Throwable, Int] @definedAt[E1] = {
    case e: E1 => 10
  }
  val pf2: PartialFunction[Throwable, Int] @definedAt[E2] = {
    case e: E2 => 20
  }
  val pf3: PartialFunction[Throwable, Int] @definedAt[E1 | E2] = pf1 orElse pf2


  /**
   * guarded *union?) intersection types
   *
   */


  def myTry[T](body: => T) = new {
    def myCatch(handler: PartialFunction[Throwable, T]): T @pc(body, mask = caughtBy(handler)) @pc(handler(%)) = try {
      body
    } catch {

      /**
       *  in princible, we want "catch handler", but that is not allowed
       *
       * the exception analysis has to figure out a lot of things to get the below working:
       *  - that in the "then" branch, handler(e) is defined, i.e. won't throw MatchError
       *  - that "e" is no more than the exceptions of "body", so "throw e" is covered by @pc(body). related to forwarding, see maks4 above.
       *  - that "e" cannot be any of the effects where "handler" has @definedAt, i.e. that these are masked
       */

      case e =>
        if (handler.isDefinedAt(e)) handler(e)
        else throw e

        /* another way:
        try {
          handler(e)
        } catch {
          case me: MatchError => throw e
        }
        */
    }
  }

  myTry {
    if (math.random < 0.5) throw new E1
    10
  } myCatch {
    case e: E1 => 11
  }










  // STATE (a first example)


  case class write(v: Var[_]) extends Effect
  case class read(v: Var[_]) extends Effect

  case class Var[T](var x: T)

  def withVar[T, R](v: Var[T])(body: Var[T] => R): R @pc(body.apply(v)) = body(v)

  withVar(new Var(10)) ({ (v: Var[Int]) =>
    v.x = -1 : @read(v)
    println(v.x) : @write(v)
  }: (Var[Int] => Unit) { def apply(v: Var[Int]): Unit @read(v) @write(v) }): @pure

  // pure because when @read(v) and @write(v) escapes the scope of "v", the effect is no longer visible.











  // @TODO: allow users to overrule effect checking system, introduce some effect-cast!
  // e.g. when using complicated longic in a case statement of a catch block, the system can't figure it out.







  // @TODO: refinements prevents conversion to unit!!!
  // ((x: Int) => x + 1) : (Int => Unit) { def apply(x: Int): Unit }



}

