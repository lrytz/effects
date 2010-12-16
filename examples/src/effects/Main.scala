package effects


// effect annotations
trait Effect extends annotation.TypeConstraint

// masking only on effect params and param calls!
// class mask(effects: Effect*) extends TypeConstraint

case class ep(name: Symbol /*, bounds: Effect* */) extends Effect

// @TODO: is `pc` really a TypeConstraint? Look at the forwarding example, there it isn't really.
// but otherwise, effects have to be TypeConstraints, this will make the applyFirst example work.
case class pc(call: Any, mask: Seq[Effect] = Nil, propagate: Seq[Effect] = Nil) extends Effect
case class pcs(calls: Any*) extends Effect

case class masked(eff: Effect, mask: Seq[Effect]) extends Effect

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




  // functional values

  val f: (B => String) { def apply(b: B): String @pc(b.g) } = (b: B) => b.g
  // val f: (b: B) => String @pc(b.g) = (b: B) => b.g


  // @TODO: different notations for functions types with effect: refinement, annot on return type



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



  // arguments in param calls

  class Args1 {
    def f(x: Int): Int @throws[E1 | E2] = x + 1
  }

  class Args2 extends Args1 {
    override def f(x: Int): Int @throws[E1] = x + 2
  }

  // using an existential type
  def pcArgs1(a: Args1): Int @pc(a.f(x)) forSome {val x: Int} = a.f(10)

  // using an anonymous function
  def pcArgs2(a: Args1): Int @pc((x: Int) => a.f(x)) = a.f(10)

  // using the placeholder syntax for anonymous functions
  def pcArgs3(a: Args1): Int @pc(a.f(_: Int)) = a.f(10)

  // using a special value "%"
  def pcArgs4(a: Args1): Int @pc(a.f(%)) = a.f(10)

  // partially applied function
  def pcArgs5(a: Args1): Int @pc(a.f _) = a.f(10)

  pcArgs1(new Args2): @throws[E1]




  // param-call arguments refering to arguments of the method

  def app(a: A, f: A => String): String @pc(f.apply(a)) = f(a)

  app(new A1, ((a: A) => a.f.g): (A => String) { def apply(a: A): String @pc(a.f.g) }): @throws[E1]

  // or:    app(new A1, a => (a.f.g: String @pc(a.f.g))): @throws[E1]

  // later: app(new A1, (a => a.f.g): (a: A => String @pc(a.f.g))): @throws[E1]




  // pc with overloaded method

  class Ovrl {
    def foo(a: Object, b: String): String @throws[E1] = ""
    def foo(a: String, b: String): String @throws[E2] = a + b
  }


  def ovr1(o: Ovrl): String @pc(o.foo(a, b)) forSome {val a: String; val b: String} =
    o.foo("far", "bar")

  // selects the more specific (String, String)
  def ovr2(o: Ovrl): String @pc(o.foo _) = o.foo("far", "bar")

  def ovr3(o: Ovrl): String @pc(o.foo(_: Object, _: String)) =
    o.foo(new Object, "dlkfj")

  //o.foo(%, %) would work (both are applicable) and select (String, String)
  def ovr4(o: Ovrl): String @pc(o.foo(% : Object, % : String)) =
    o.foo(new Object, "flu")





  // transitive closure: pc-effect of "trans" is a pc-effect of "bar",
  // which is the actual effect

  class C0a { def baz: String @throws[E1 | E2] = "" }
  class C0b extends C0a { override def baz: String @throws[E1] = "beeeh" }

  class C1a { def bar(c: C0a): String @pc(c.baz) = c.baz }
  class C1b extends C1a { override def bar(c: C0a): String = "me pure" }

  def trans(c: C1a): String @pc(c.bar(c0)) forSome {val c0: C0b} = c.bar(new C0b)

  // we use the information that "bar" is called, so the following can be pure:
  trans(new C1b): @pure

  // we use the information that "bar" is called with argument of C0b:
  trans(new C1a): @throws[E1]






  // converting to functional values, eta-expansion

  def map[A, B](l: List[A], f: A => B): List[B] @pc(f.apply(%)) = l match {
    case x :: xs => f(x) :: map(xs, f)
    case Nil => Nil
  }


  // works because the parameter "f" is forwareded directly to map, which has a @pc on its corresponding parameter!!!
  val mapPrims: ((Int => Int) => List[Int]) { def apply(f: Int => Int): List[Int] @pc(f.apply(%)) } = (f: Int => Int) => map(List(1, 3, 5, 7, 11, 13), f)
  mapPrims(x => { if (x > 10) throw new E1 else x + 1 }): @throws[E1]

  // @TODO: the refinement type breaks type inference, also here
  // again, works because of param forwarding, but we have to look at it after eta-expansion (should be fine).
  val mapInts: ((List[Int], Int => Int) => List[Int]) { def apply(l: List[Int], f: Int => Int): List[Int] @pc(f.apply(%)) } = (map _): ((List[Int], Int => Int) => List[Int])


  // @TODO error! cannot convert method with dependent method type to a functional value. to be seen.

//  def dep(a: A, f: A => B): B @pc(f.apply(a)) = f(a)
//  dep _








  // explicit effect parameters for polymorphism when ParamCall doesn't help. using an additional type param.
  // the @polyEff annotation *always* goes to a method's return type (in a refinement). sugar for functions.

  class polyEff1[e <: Effect] extends Effect

  def applyFst1[e <: Effect](a: A, fs: List[A => String @polyEff1[e]]): String @polyEff1[e] = fs match {
    case f :: _ => f(a)
    case _ => ""
  }



  // using implicits, inserted by the compiler. (no error here due to a bug: dependent type not detected)

  class polyEff2(e: Effect) extends Effect

  def applyFst2(a: A, fs: List[A => String @polyEff2(eff)])(implicit eff: Effect): String @polyEff2(eff) = fs match {
    case f :: _ => f(a)
    case _ => ""
  }

  applyFst2(new A, List(a => { throw new E1; "dlskfj" }))(throws[E1])



  // problem in these two: can't talk about the type of the argument that was used. something
  // like this, but here we'd need to make sure not to use the same effect param twice!

  class polyEff3(e: Effect) extends Effect
  class polyEff3App(e: Effect, arg: Any) extends Effect

  def applyFst3(a: A, fs: List[A => String @polyEff3(eff)])(implicit eff: Effect): String @polyEff3App(eff, %: A) = fs match {
    case f :: _ => f(a)
    case _ => ""
  }


  /**
   * Another idea: give value names on type parameters.
   *
   * trait List[(i: +A)] {
   *   def hd: (i: A)
   *   def tl: List[(i: A)]
   * }
   * case class Cons[(i: +A)](hd: (i: A), tl: List[(i: A)] extends List[(i: A)]
   * case object Nil extends List[(n: Nothing)] // (equivalent ot List[Nothing])
   *
   * def f(l: List[(f: A => B)]): B @pc(f.apply(_: A)) = l match {
   *   case Cons(x, xs) => x(new A)    // type of x: (f: A)
   *   case _ => new B
   * }
   *
   *
   * Names could maybe be done in annotation world (?)
   *
   */




  // curried definitions

  def applyFst3(fs: List[A => String @polyEff2(eff)])(gs: List[A => String @polyEff2(eff)])(implicit eff: Effect): String @polyEff2(eff) =
    if (!fs.isEmpty && !gs.isEmpty) fs.head(new A) + gs.head(new A)
    else ""

  // this should proabbly not be allowed, the first param list should fix "eff" to be "throws[E1]"
  applyFst3(List(a => {throw new E1; "foo"}))(List((a: A) => {throw new E2; "bar"}))(throws[E1 | E2])


  // this should fix "eff" to "throws[E1]" and only allow that for the second
  // argument (take in account variance! pure should be fine!)

  // doesn't work because implicit value is not inserted, that has to be done by the compiler
  // val apf3 = applyFst3(List(a => {throw new E1; "floo"})) _
  // apf3(List(a => "blup"))


  // not so nice:
  def applyFst4(fs: List[A => String])(gs: List[A => String @polyEff2(eff)])(implicit eff: Effect): String @polyEff2(eff) =
      if (!gs.isEmpty) gs.head(new A)
      else ""

  // BAD: compiler tries to insert the implicit... so effect has to be known
  // val m = applyFst4(List()) _

  // BUT: similar for type params:
  // def f[A](x: Int)(y: A) = y
  // f(1) _         // <<-- has type (Nothing) => Nothing






  // more ad-hoc: using an @ep annotation. could still be encoded internally using the implicits

  def applyFirst5(a: A, fs: List[A => String @ep('e)]): String @ep('e) = fs match {
    case f :: _ => f(a)
    case _ => ""
  }
  //@TODO: need param type (a: A) because of refinement
  applyFirst5(new A1, List((a: A) => (a.f.g: @pc(a.f.g))): List[(A => String) {def apply(a: A): String @pc(a.f.g)}]): @throws[E1 | E2]




  /**
   * Upper bound on effect
   *
   *  - an effect on a method's return type (in a refinement) means a bound
   *
   *  - in general, they can only be attached to method return types using type refinements
   *    => Allow short syntax for functions. A => B @throws[E1] means
   *                  (A => B) { def apply(a: A): B @throws[E1] }
   *
   *
   *
   *  - question of domains. does it limit the effect only in one domain? or require others pure?
   */



  // bounds: examples with exceptions

  def pureForall[A](l: List[A], p: A => Boolean @pure): Boolean @pure = l match {
    case x :: xs => p(x) && pureForall(xs, p)
    case Nil => true
  }

  pureForall(List(1,2,3), (x: Int) => x < 10)
  // should be rejected
  pureForall(List(1, 2, 3), (x: Int) => {
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


  def boundExec(b: B, f: B => String @throws[E1]): String @pc(f.apply(_: B)) = {
    f(b)
  }

  (boundExec(new B, b => { throw new E1 }): @throws[E1]) // OK
  (boundExec(new B, b => "dlkfj"): @pure) // OK
  boundExec(new B, b => { throw new E2 }) // reject




  /**
   * Bound in covariant position: ok, but doesn't really make sense. One could just
   * as well have no bound, the result would be the same.
   */

  def lowB(f: (A => String @throws[E1]) => String): String @pc(f.apply(_: (A => String @pure))) =
    f(a => "dlkfj")

  /**
   * "funk" takes an m: (A => String) with upper bound @throws[E1].
   * It has effects @pc(m.apply) and @trhows[E2].
   */
  val funk = ((m: A => String @throws[E1]) => {
    if (math.random < 0.4) throw new E2;
    m(new A): @pc(m.apply(_: A))
  }): ((A => String @throws[E1]) => String) {def apply(m: (A => String @throws[E1])): String @throws[E2] @pc(m.apply(_: A))}

  // lowB has effect @pc(funk.apply(_: (A => String @pure))), i.e. only @throws[E2]
  lowB(funk): @throws[E2]





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
   *  - can an argument function mask something? Probably not, how should it? One needs to
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


  class fooEff extends Effect
  object fooEff extends Effect

  def fooIntro(): Unit @fooEff = {
    ()
  }

  def fooMask[T](body: => T): T @pc(body, mask = fooEff) = {
    body
  }


  def fooFul(x: Int): Int @fooEff = {
    fooIntro()
    x + 10
  }

  (fooMask { fooFul(10) } + 2): @pure




  // polymorphic masking

  class FM1 {
    def mask[T](body: => T): T @pc(body) = {
      body
    }
  }

  class FM2 extends FM1 {
    // overriding: need to mask more
    override def mask[T](body: => T): T @pc(body, mask = fooEff) = {
      body
    }
  }

  def polyMask(fm: FM1, x: Int): Int @pc(fm.mask(_: Int @fooEff /* in fact, (=> Int @fooEff) */)) = {
    fm.mask {
      fooFul(x)
    }
  }

  polyMask(new FM2, 20): @pure





  // every function can mask effects. example:

  def incWithE(x: Int): Int @throws[E1] = {
    if (math.random < 0.1) throw new E1
    else x + 1
  }

  // pc cand do both: yield AND/OR mask an effect.

  // the effect throws[E1] DOES happen! f's argument is not call-by-name, so
  // incWithE(99) IS evaluated, which DOES have an effect.
  def funMask[T](f: Int => T): T @throws[E1] @pc(f.apply(_: Int)) = {
    f(incWithE(99))
  }


  // delay execution of f's argument (could also use by-name param)
  def funMaskD[T](f: (() => Int) => T): T @pc(f.apply(_: (() => Int @throws[E1]))) = {
    f(() => incWithE(99))
  }

  val arg: ((() => Int) => Int) { def apply(f: () => Int): Int @pc(f.apply(), mask = throws[E1]) } = (f: () => Int) => {
    try { f() }
    catch { case e: E1 => 2 }
  }

  funMaskD(arg): @pure




  // no masking here, because there's no effect- or handler-polymorphism
  def safeFoo: Unit = try {
    foo
  } catch {
    case e: E2 => ()
  }


  // maks depends on handler.
  def withHandler(h: PartialFunction[Throwable, Unit]): Unit @masked(throws[E2], caughtBy(h)) = try {
    foo
  } catch h



  // masking on effect-polymorphic methods
  def mask1(b: B): String @pc(b.g, mask = throws[E1]) = try {
    b.g
  } catch {
    case e: E1 => "got e1"
  }

  (mask1(new B): @throws[E2])
  mask1(new B1): @pure



  // "mask = x"      <==>  "propagate all except x"
  // "propagate = x  <==>  "mask all except x"


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




  // propagating exceptions (like "anchored exceptions" paper)

  def mask3(f: Int => String): String @pc(f.apply(%), mask = throws[Throwable], propagate = throws[E2]) = try {
    f(10)
  } catch {
    case e: E2 => throw e
    case e => "got some exception"
  }

  mask3((x: Int) => { throw new E1; "dlkfj" }): @pure


  // here, the "propagates" is not needed, this is clear from the @pc.

  def mask4(b: B): String @pc(b.g, mask = throws[E1], propagate = throws[E2]) = try {
    b.g
  } catch {
    case e: E2 => throw e
    case e: E1 => "got e1"
  }

  mask4(new B1): @pure




  // here, E2 is also a latent effect of mask5
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
   * our effect system express arbitrary pluggable type systems?
   *
   */

  class definedAt[E <: Throwable] extends Effect
  def caughtBy[T](pf: PartialFunction[Throwable, T]): Effect = throw new Error()

  val pf1: PartialFunction[Throwable, Int] @definedAt[E1] = {
    case e: E1 => 10
  }
  val pf2: PartialFunction[Throwable, Int] @definedAt[E2] = {
    case e: E2 => 20
  }
  val pf3: PartialFunction[Throwable, Int] @definedAt[E1 | E2] = pf1 orElse pf2



  def myTry[T](body: => T) = new {
    def myCatch(handler: PartialFunction[Throwable, T]): T @pc(body, mask = caughtBy(handler)) @pc(handler(%)) = try {
      body
    } catch handler
  }

  // the following two should also be recognized
/*
  case e =>
    if (handler.isDefinedAt(e)) handler(e)
    else throw e

  case e =>
    try {
      handler(e)
    } catch {
      case me: MatchError => throw e
    }
*/



  (myTry {
    if (math.random < 0.5) throw new E1
    10
  } myCatch {
    case e: E1 => 11
  }): @pure

  (myTry {
    if (math.random < 0.1) throw new E1
    10
  } myCatch pf2): @throws[E1]



  val tried = (myTry {
    if (math.random < 0.5) throw new E1
    10
  }): { def myCatch(h: PartialFunction[Throwable, Int]): Int @masked(throws[E1], caughtBy(h)) }


  (tried myCatch pf1): @pure






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

