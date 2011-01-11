package effects
package colls

// @TODO: where / how to annotate the constructor? it should be on the return type!?!
trait Bldr[-Elem, +To] {

  // effect is something like "modifies(this)", meaning "can modifies its fileds".
  //  ==> when an instance of Bldr is a local variable, these effects can be masked.

  def +=(elem: Elem): this.type /* @modifies(this) */

  def result(): To @pure
}

trait CBF[-From, -Elem, +To] {
  def apply(from: From): Bldr[Elem, To] @pure
}



trait TravLk[+A, +Repr] { self: Repr =>
  protected[this] def newBuilder: Bldr[A, Repr] @pure

  def foreach[U](f: A => U): Unit @pure @pc(f.apply(a)) forSome {val a: A}

  def isEmpty: Boolean @pure = {
    var result = true
    for (x <- this) {
      result = false
    } // @pc(this.foreach(f)) forSome {val f: A => Unit @write(result)}

    // The effect of writing a local variable can be masked
    result
  }

  def drop(n: Int): Repr @pure = {
    val b = newBuilder
    var i = 0
    for (x <- this) {
      if (i >= n) b += x // @modifies(b)
      i += 1 // @write(i)
    } // @pc(this.foreach(f)) forSome {val f: A => Unit @modifies(b) @write(i)}

    // Both effects can be masked: i and b are local, so writes to them are not visible.
    b.result
  }

  def head: A @pure @throws[NoSuchElementException] = {
    var result: Option[A] = None
    for (x <- this) {
      if (result.isEmpty) result = Some(x) // @write(result)
    } // @pc(this.foreach(f)) forSome {val f: A => Unit @write(result)}

    // result is local => writing to it will be masked
    result.getOrElse(throw new NoSuchElementException)
  }

  def tail: Repr @pure @throws[UnsupportedOperationException] = {
    if (isEmpty) throw new UnsupportedOperationException("empty.tail")
    drop(1)
  }

  def filter(p: A => Boolean): Repr @pure @pc(pc.apply(a)) forSome {val a: A} = {
    val b = newBuilder
    for (x <- this) // @pc(this.foreach(f)) forSome {val f: A => Unit @pc(p.apply(%)) @modifies(b)}
      if (p(x)) b += x
    b.result // b is local => can mask @modifies(b)
  }

  def map[B, That](f: A => B)(implicit bf: CBF[Repr, B, That]): That @pc(f.apply(x)) forSome {val x: A} = {
    // @TODO: cast due to intellij bug (youtrack.jetbrains.net/issue/SCL-2480)
    val b = bf(self.asInstanceOf[Repr]) // @pure, bf.apply is pure
    for (x <- this) b += f(x) // @pc(this.foreach(f)) forSome {val f: A => Unit @modifies(b) @pc(f.apply(x)) forSome {val x: A}}
    b.result // b is local => can mask @modifies(b)
  }
}



trait GenTravTmpl[+A, +CC[X] <: Trav[X]] {
  def companion: GenCpn[CC] @pure; // @TODO: semicolon due to intellij bug
  protected[this] def newBuilder: Bldr[A, CC[A]] @pure = companion.newBuilder[A]
  def genericBuilder[B]: Bldr[B, CC[B]] @pure = companion.newBuilder[B]
}

abstract class GenCpn[+CC[X] <: Trav[X]] {
  type Coll = CC[_]
  def newBuilder[A]: Bldr[A, CC[A]] @pure;
  def empty[A]: CC[A] @pure = newBuilder[A].result
}

abstract class TravFct[CC[X] <: Trav[X] with GenTravTmpl[X, CC]] extends GenCpn[CC] {
  class GCBF[A] extends CBF[CC[_], A, CC[A]] {
    def apply(from: Coll): Bldr[A, CC[A]] @pure = from.genericBuilder[A]
  }
}



trait Trav[+A] extends TravLk[A, Trav[A]] with GenTravTmpl[A, Trav] {
  def companion: GenCpn[Trav] @pure = Trav
}

object Trav extends TravFct[Trav] {
  implicit def canBuildFrom[A]: CBF[Coll, A, Trav[A]] @pure = new GCBF[A]

  def newBuilder[A]: Bldr[A, Trav[A]] @pure = new LstBldr
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
  def newBuilder[A]: Bldr[A, Itrbl[A]] @pure = new LstBldr
}



trait SqLk[+A, +Repr <: SqLk[A, Repr]] extends ItrblLk[A, Repr] { self: Repr =>
  def length: Int @pure;
  def apply(idx: Int): A // @TODO: what effect? @throws[NoSuchElementException], or any effect?

  def iterator: Itor[A] @pure = new Itor[A] {
    var these = self
    def hasNext: Boolean @pure = !these.isEmpty
    def next: A @pure @throws[NoSuchElementException | UnsupportedOperationException] /* @modifies(these) */ =
      if (hasNext) {
        // hasNext =>  "head" / "tail" will succeed. but the system can't track that.
        val result = these.head; these = these.tail; result
      } else Itor.empty.next
  }
}

abstract class SqFct[CC[X] <: Sq[X] with GenTravTmpl[X, CC]] extends TravFct[CC] {
  // adds "unapplySeq" in real; otherwise not needed, could use TravFct
}

trait Sq[+A] extends Itrbl[A] with GenTravTmpl[A, Sq] with SqLk[A, Sq[A]] {
  override def companion: GenCpn[Sq] @pure = Sq
}

object Sq extends SqFct[Sq] {
  def newBuilder[A]: Bldr[A, Sq[A]] @pure = new LstBldr
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
  val b = new collection.mutable.ListBuffer[A]()
  def +=(a: A) /* @modifies(b) */ = { b += a; this }
  def result: Lst[A] @pure = Lst(b: _*)
}

object Lst extends SqFct[Lst] {
  def apply[A](elems: A*): Lst[A] @pure = {
    elems.foldRight(nl: Lst[A])((a, res) => cns(a, res))
  }
  def newBuilder[A]: Bldr[A, Lst[A]] @pure = new LstBldr[A]
  override def empty[A]: Lst[A] @pure = nl
}


