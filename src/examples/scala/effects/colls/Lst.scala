package effects
package colls


trait Bldr[-Elem, +To] {
  def +=(elem: Elem): this.type
  def result(): To
}

trait CBF[-From, -Elem, +To] {
  def apply(from: From): Bldr[Elem, To]
}



trait TravLk[+A, +Repr] { self: Repr =>
  protected[this] def newBuilder: Bldr[A, Repr]

  def foreach[U](f: A => U): Unit

  def isEmpty: Boolean = {
    var result = true
    for (x <- this) {
      result = false
    }
    result
  }

  def drop(n: Int): Repr = {
    val b = newBuilder
    var i = 0
    for (x <- this) {
      if (i >= n) b += x
      i += 1
    }
    b.result()
  }

  def head: A = {
    var result: Option[A] = None
    for (x <- this) {
      if (result.isEmpty) result = Some(x)
    }
    result.getOrElse(throw new NoSuchElementException)
  }

  def tail: Repr = {
    if (isEmpty) throw new UnsupportedOperationException("empty.tail")
    drop(1)
  }

  def filter(p: A => Boolean): Repr = {
    val b = newBuilder
    for (x <- this)
      if (p(x)) b += x
    b.result()
  }

  def map[B, That](f: A => B)(implicit bf: CBF[Repr, B, That]): That = {
    val b = bf(self.asInstanceOf[Repr]) // @TODO: cast due to intellij bug (youtrack.jetbrains.net/issue/SCL-2480)
    for (x <- this) b += f(x)
    b.result()
  }
}



trait GenTravTmpl[+A, +CC[X] <: Trav[X]] {
  def companion: GenCpn[CC]
  protected[this] def newBuilder: Bldr[A, CC[A]] = companion.newBuilder[A]
  def genericBuilder[B]: Bldr[B, CC[B]] = companion.newBuilder[B]
}

abstract class GenCpn[+CC[X] <: Trav[X]] {
  type Coll = CC[_]
  def newBuilder[A]: Bldr[A, CC[A]]
  def empty[A]: CC[A] = newBuilder[A].result()
}

abstract class TravFct[CC[X] <: Trav[X] with GenTravTmpl[X, CC]] extends GenCpn[CC] {
  class GCBF[A] extends CBF[CC[_], A, CC[A]] {
    def apply(from: Coll) = from.genericBuilder[A]
  }
}



trait Trav[+A] extends TravLk[A, Trav[A]] with GenTravTmpl[A, Trav] {
  def companion: GenCpn[Trav] = Trav
}

object Trav extends TravFct[Trav] {
  implicit def canBuildFrom[A]: CBF[Coll, A, Trav[A]] = new GCBF[A]

  def newBuilder[A]: Bldr[A, Trav[A]] = new LstBldr
}



trait Itor[+A] {
  def hasNext: Boolean
  def next(): A
  def isEmpty: Boolean = !hasNext
  def foreach[U](f: A =>  U) { while (hasNext) f(next()) }
}

object Itor {
  val empty = new Itor[Nothing] {
    def hasNext: Boolean = false
    def next(): Nothing = throw new NoSuchElementException("next on empty iterator")
  }
}



trait ItrblLk[+A, +Repr] extends TravLk[A, Repr] { self: Repr =>
  def iterator: Itor[A]
  def foreach[U](f: A => U): Unit =
    iterator.foreach(f)
}

trait Itrbl[+A] extends Trav[A] with GenTravTmpl[A, Itrbl] with ItrblLk[A, Itrbl[A]] {
  override def companion: GenCpn[Itrbl] = Itrbl
}
object Itrbl extends TravFct[Itrbl] {
  def newBuilder[A]: Bldr[A, Itrbl[A]] = new LstBldr
}



trait SqLk[+A, +Repr <: SqLk[A, Repr]] extends ItrblLk[A, Repr] { self: Repr =>
  def length: Int
  def apply(idx: Int): A

  def iterator: Itor[A] = new Itor[A] {
    var these = self
    def hasNext: Boolean = !these.isEmpty
    def next(): A =
      if (hasNext) {
        val result = these.head; these = these.tail; result
      } else Itor.empty.next()
  }
}

abstract class SqFct[CC[X] <: Sq[X] with GenTravTmpl[X, CC]] extends TravFct[CC] {
  // adds "unapplySeq" in real; otherwise not needed, could use TravFct
}

trait Sq[+A] extends Itrbl[A] with GenTravTmpl[A, Sq] with SqLk[A, Sq[A]] {
  override def companion: GenCpn[Sq] = Sq
}

object Sq extends SqFct[Sq] {
  def newBuilder[A]: Bldr[A, Sq[A]] = new LstBldr
}



sealed abstract class Lst[+A] extends Sq[A] with GenTravTmpl[A, Lst] with SqLk[A, Lst[A]] {
  def apply(idx: Int): A = if (idx == 0) head else tail(idx - 1)
  def length: Int = if (isEmpty) 0 else 1+tail.length // @TODO: return type due to intellij bug
  override def companion: GenCpn[Lst] = Lst
}

final case class cns[A](override val head: A, override val tail: Lst[A]) extends Lst[A] {
  override def isEmpty = false
}

case object nl extends Lst[Nothing] {
  override def isEmpty = true
}

class LstBldr[A] extends Bldr[A, Lst[A]] {
  val b = new collection.mutable.ListBuffer[A]()
  def +=(a: A) = { b += a; this }
  def result(): Lst[A] = Lst(b: _*)
}

object Lst extends SqFct[Lst] {
  def apply[A](elems: A*) = {
    elems.foldRight(nl: Lst[A])((a, res) => cns(a, res))
  }
  def newBuilder[A]: Bldr[A, Lst[A]] = new LstBldr[A]
  override def empty[A]: Lst[A] = nl
}
