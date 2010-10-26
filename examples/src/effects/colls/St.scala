package effects.colls

trait Addable[A, +Repr <: Addable[A, Repr]] { self: Repr =>
  def +(elem: A): Repr
}

trait StLk[A, +This <: StLk[A, This] with St[A]] extends ItrblLk[A, This] with Addable[A, This] { self: This =>
  def empty: This
  override protected[this] def newBuilder: Bldr[A, This] = new AddBldr[A, This](empty.asInstanceOf[This]) // @TODO: why cast??? bug?
  def contains(elem: A): Boolean
  def + (elem: A): This
  def - (elem: A): This
  def apply(elem: A): Boolean = contains(elem)
}

class AddBldr[Elem, To <: Addable[Elem, To] with Itrbl[Elem] with ItrblLk[Elem, To]](empty: To) extends Bldr[Elem, To] {
  protected var elems: To = empty
  def +=(x: Elem): this.type = { elems = elems + x; this }
  def clear() { elems = empty }
  def result: To = elems
}

abstract class StFct[CC[X] <: St[X] with StLk[X, CC[X]]] extends GenCpn[CC] {
  def newBuilder[A]: Bldr[A, CC[A]] = new AddBldr[A, CC[A]](empty[A])
  def setCanBuildFrom[A] = new CBF[CC[_], A, CC[A]] {
    def apply(from: CC[_]) = newBuilder[A]
  }
}

trait GenStTmpl[A, +CC[X] <: St[X]] extends GenTravTmpl[A, CC] {
  def empty: CC[A] = companion.empty[A]
}

trait St[A] extends (A => Boolean) with Itrbl[A] with GenStTmpl[A, St] with StLk[A, St[A]] {
  override def companion: GenCpn[St] = St
}

object St extends StFct[St] {
  override def empty[A]: St[A] = new HSt[A]()
  implicit def canBuildFrom[A]: CBF[Coll, A, St[A]] = setCanBuildFrom[A]
}


class HSt[A](private val els: collection.immutable.Set[A] = new collection.immutable.HashSet[A]()) extends St[A] with GenStTmpl[A, HSt] with StLk[A, HSt[A]] { self =>
  override def companion: GenCpn[HSt] = HSt

  def size = els.size
  def contains(elem: A): Boolean = els(elem)
  def + (elem: A): HSt[A] = new HSt[A](self.els + elem)
  def - (elem: A): HSt[A] = new HSt[A](self.els - elem)
  def iterator: Itor[A] = new Itor[A] {
    val it = els.iterator
    def hasNext: Boolean = it.hasNext
    def next(): A = it.next()
  }
  override def foreach[U](f: A =>  U): Unit = els.foreach[U](f)
}

object HSt extends StFct[HSt] {
  implicit def canBuildFrom[A]: CBF[Coll, A, HSt[A]] = setCanBuildFrom[A]
  override def empty[A]: HSt[A] = new HSt[A]()
}
