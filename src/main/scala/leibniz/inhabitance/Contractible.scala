package leibniz.inhabitance

import leibniz._
import leibniz.internal.Unsafe

/**
  * Witnesses that all values `(a: A)` are equal and that [[A]] is inhabited.
  */
sealed trait Contractible[A] {
  def inhabited: Inhabited[A]
  def prop: Proposition[A]

  def contract[B](implicit p: B <~< A, q: Inhabited[B]): B === A
}
object Contractible {
  private[this] final class Single[A](val inhabited: Inhabited[A], val prop: Proposition[A]) extends Contractible[A] {
    def contract[B](implicit p: B <~< A, B: Inhabited[B]): B === A =
      prop.equal[B, A](p, As.refl[A], B, inhabited)
  }

  def apply[A](implicit A: Contractible[A]): Contractible[A] = A

  def construct[A](implicit A: Inhabited[A], prop: Proposition[A]): Contractible[A] =
    new Single[A](A, prop)

  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Contractible[A] =
    construct[A](Inhabited.witness(A.value), Proposition.singleton[A])

  implicit def proposition[A]: Proposition[Contractible[A]] =
    Proposition.force[Contractible[A]](Unsafe.unsafe)
}