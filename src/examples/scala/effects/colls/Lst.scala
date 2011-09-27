package effects
package colls

// @TODO: where / how to annotate the constructor? it should be on the return type!?!
trait Bldr[-Elem, +To] {
  def +=(elem: Elem): this.type @pure @mod(this)
  def result(): To @pure
}

trait CBF[-From, -Elem, +To] {
  def apply(from: From): Bldr[Elem, To] @pure @fresh // `pure` does not imply `fresh`, but only `@mod()`!
}



trait TravLk[+A, +Repr] { self: Repr =>
  protected[this] def newBuilder: Bldr[A, Repr] @pure @fresh

  def foreach[U](f: A => U): Unit @pure @pc(f.apply(a)) forSome {val a: A}

  def isEmpty: Boolean @pure = {
    var result = true
    for (x <- this) {
      result = false  // @mod(result)
    } // @mod(result)

    result // `@mod(result)` can be masked, because `result` is fresh and gets out of scope`
  }

  def drop(n: Int): Repr @pure = {
    val b = newBuilder // @fresh(b)
    var i = 0
    for (x <- this) {
      if (i >= n) b += x // @mod(b)
      i += 1 // @mod(i)
    } // @mod(i, b)

    // Both effects can be masked: i is local, b is fresh, so writes to them are not visible.
    b.result()
  }

  def head: A @pure @throws[NoSuchElementException] = {
    var result: Option[A] = None
    for (x <- this) {
      if (result.isEmpty) result = Some(x) // @mod(result)
    } // @mod(result)

    // getOrElse has effect of its argument. @mod(result) is masked
    result.getOrElse(throw new NoSuchElementException)
  }

  def tail: Repr @pure @throws[UnsupportedOperationException] = {
    if (isEmpty) throw new UnsupportedOperationException("empty.tail")
    drop(1)
  }

  def filter(p: A => Boolean): Repr @pure @pc(pc.apply(a)) forSome {val a: A} = {
    val b = newBuilder // @fresh(b)
    for (x <- this)
      if (p(x)) b += x // @mod(b) @pc(p.apply(_))
    b.result() // b is local => can mask @mod(b), because @fresh(b)
  }

  def map[B, That](f: A => B)(implicit bf: CBF[Repr, B, That]): That @pc(f.apply(%)) = {
    val b = bf(self) // @fresh(b) @pure (bf.apply is pure)
    for (x <- this) b += f(x) // @mod(b) @pc(f.apply(%))
    b.result() // @fresh(b) => mask @mod(b)
  }
}



trait GenTravTmpl[+A, +CC[X] <: Trav[X]] {
  def companion: GenCpn[CC] @pure; // @TODO: semicolon due to intellij bug
  protected[this] def newBuilder: Bldr[A, CC[A]] @pure @fresh = companion.newBuilder[A]
  def genericBuilder[B]: Bldr[B, CC[B]] @pure @fresh = companion.newBuilder[B]
}

abstract class GenCpn[+CC[X] <: Trav[X]] {
  type Coll = CC[_]
  def newBuilder[A]: Bldr[A, CC[A]] @pure @fresh;
  def empty[A]: CC[A] @pure = newBuilder[A].result()
}

abstract class TravFct[CC[X] <: Trav[X] with GenTravTmpl[X, CC]] extends GenCpn[CC] {
  class GCBF[A] extends CBF[CC[_], A, CC[A]] {
    def apply(from: Coll): Bldr[A, CC[A]] @pure @fresh = from.genericBuilder[A]
  }
}



trait Trav[+A] extends TravLk[A, Trav[A]] with GenTravTmpl[A, Trav] {
  def companion: GenCpn[Trav] @pure = Trav
}

object Trav extends TravFct[Trav] {
  implicit def canBuildFrom[A]: CBF[Coll, A, Trav[A]] @pure = new GCBF[A]

  def newBuilder[A]: Bldr[A, Trav[A]] @fresh = new LstBldr
}



trait Itor[+A] {
  def hasNext: Boolean @pure;
  def next(): A // @TODO: what effect? @throws[NoSuchElementException | UnsupportedOperationException] at least. Allow any effect?
  def isEmpty: Boolean @pure = !hasNext
  def foreach[U](f: A =>  U): Unit @pure @pc(f.apply(a)) forSome {val a: A} = { while (hasNext) f(next()) }
}

object Itor {
  val empty = new Itor[Nothing] {
    def hasNext: Boolean @pure = false
    def next(): Nothing @throws[NoSuchElementException] = throw new NoSuchElementException("next on empty iterator")
  }
}



trait ItrblLk[+A, +Repr] extends TravLk[A, Repr] { self: Repr =>
  def iterator: Itor[A] @pure;
  def foreach[U](f: A => U): Unit @pure @pc(f.apply(a)) forSome {val a: A} =
    iterator.foreach(f)
}

trait Itrbl[+A] extends Trav[A] with GenTravTmpl[A, Itrbl] with ItrblLk[A, Itrbl[A]] {
  override def companion: GenCpn[Itrbl] @pure = Itrbl
}
object Itrbl extends TravFct[Itrbl] {
  def newBuilder[A]: Bldr[A, Itrbl[A]] @pure @fresh = new LstBldr
}



trait SqLk[+A, +Repr <: SqLk[A, Repr]] extends ItrblLk[A, Repr] { self: Repr =>
  def length: Int @pure;
  def apply(idx: Int): A // @TODO: what effect? @throws[NoSuchElementException], or any effect?

  def iterator: Itor[A] @pure = new Itor[A] {
    var these = self // not @local!
    def hasNext: Boolean @pure = !these.isEmpty
    def next(): A @pure @throws[NoSuchElementException | UnsupportedOperationException] @mod(this) =
      if (hasNext) {
        // hasNext =>  "head" / "tail" will succeed. but the system can't track that.
        val result = these.head; these = these.tail; result
      } else Itor.empty.next()
  }
}

abstract class SqFct[CC[X] <: Sq[X] with GenTravTmpl[X, CC]] extends TravFct[CC] {
  // adds "unapplySeq" in real; otherwise not needed, could use TravFct
}

trait Sq[+A] extends Itrbl[A] with GenTravTmpl[A, Sq] with SqLk[A, Sq[A]] {
  override def companion: GenCpn[Sq] @pure = Sq
}

object Sq extends SqFct[Sq] {
  def newBuilder[A]: Bldr[A, Sq[A]] @pure @fresh = new LstBldr
}



sealed abstract class Lst[+A] extends Sq[A] with GenTravTmpl[A, Lst] with SqLk[A, Lst[A]] {
  def apply(idx: Int): A @pure @throws[NoSuchElementException | UnsupportedOperationException] = if (idx == 0) head else tail(idx - 1)
  def length: Int @pure = if (isEmpty) 0 else 1+tail.length // @TODO: return type due to intellij bug
  override def companion: GenCpn[Lst] @pure = Lst
}

// @TODO: overriding a "def" using a "val" => makes it pure. do we need to annotate that?
final case class cns[A](override val head: A, override val tail: Lst[A]) extends Lst[A] {
  override def isEmpty: Boolean @pure = false
}

case object nl extends Lst[Nothing] {
  override def isEmpty: Boolean @pure = true
}

class LstBldr[A] extends Bldr[A, Lst[A]] {
  @local val b = new collection.mutable.ListBuffer[A]()
  def +=(a: A): this.type @pure @mod(this) = {
    b += a; // @mod(this); need to know that ListBuffer.+= has effect @mod(this)
    this
  }
  def result(): Lst[A] @pure = Lst(b: _*)
}

object Lst extends SqFct[Lst] {
  def apply[A](elems: A*): Lst[A] @pure = {
    elems.foldRight(nl: Lst[A])((a, res) => cns(a, res))
  }
  def newBuilder[A]: Bldr[A, Lst[A]] @pure @fresh = new LstBldr[A]
  override def empty[A]: Lst[A] @pure = nl
}
