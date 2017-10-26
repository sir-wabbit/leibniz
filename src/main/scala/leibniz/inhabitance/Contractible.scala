package leibniz.inhabitance

import leibniz._
import leibniz.internal.Unsafe

/**
  * Witnesses that all values `(a: A)` are equal and that [[A]] is inhabited.
  */
sealed abstract class Contractible[A] {
  def inhabited: Inhabited[A]
  def prop: Proposition[A]

  def contract[B](implicit p: B <~< A, q: Inhabited[B]): B === A
}
object Contractible {
  private[this] final class Witness[A](val inhabited: Inhabited[A], val prop: Proposition[A]) extends Contractible[A] {
    def contract[B](implicit p: B <~< A, B: Inhabited[B]): B === A =
      prop.equal[B, A](p, As.refl[A], B, inhabited)
  }

  def apply[A](implicit A: Contractible[A]): Contractible[A] = A

  def witness[A](implicit inhabited: Inhabited[A], proposition: Proposition[A]): Contractible[A] =
    new Witness[A](inhabited, proposition)

  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Contractible[A] =
    witness[A](Inhabited.value(A.value), Proposition.singleton[A])

  implicit def proposition[A]: Proposition[Contractible[A]] =
    Proposition.force[Contractible[A]](Unsafe.unsafe)
}