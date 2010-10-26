package object effects {
  def % : Nothing = throw new Error("% should never be called")

  import effects.{Effect => E}

  implicit def e1Seq(e: E): List[E] = Nil
  implicit def e2Seq(es: (E, E)): List[E] = Nil
  implicit def e3Seq(es: (E, E, E)): List[E] = Nil
  implicit def e4Seq(es: (E, E, E, E)): List[E] = Nil
  implicit def e5Seq(es: (E, E, E, E, E)): List[E] = Nil
  implicit def e6Seq(es: (E, E, E, E, E, E)): List[E] = Nil
  implicit def e7Seq(es: (E, E, E, E, E, E, E)): List[E] = Nil
  implicit def e8Seq(es: (E, E, E, E, E, E, E, E)): List[E] = Nil
  implicit def e9Seq(es: (E, E, E, E, E, E, E, E, E)): List[E] = Nil
}
