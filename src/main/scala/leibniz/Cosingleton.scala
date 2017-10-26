package leibniz

sealed abstract class Cosingleton[A] {
  type Type >: A

  def equality: Eq[Type]
}
object Cosingleton {
  final class Instance[A, L <: A](val equality: Eq[A]) extends Cosingleton[L] {
    type Type = A
  }

  def apply[A]: Cosingleton[A] =
    macro internal.Whitebox.cosingleton[A]

  def witness[A, L <: A](implicit A: Eq[A]): Cosingleton[L] =
    new Instance[A, L](A)
}
