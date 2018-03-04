package leibniz

import internal.ImplicationMacro

object Implies {
  type Base <: AnyRef
  type Tag
  type Type[A, B] <: Base with Tag

  def apply[A, B](implicit ev: Type[A, B]): Type[A, B] = ev

  implicit def mkImplies[A, B]: Type[A, B] =
    macro ImplicationMacro.mkImplies[A, B]

  implicit def run[A, B](implicit A: A, AB: A |- B): B =
    AB.asInstanceOf[A => B].apply(A)
}