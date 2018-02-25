package leibniz.inhabitance

import leibniz._
import leibniz.internal.Unsafe

/**
  * Witnesses that all values `(a: A)` are equal and that [[A]] is inhabited.
  */
final case class Contractible[A](inhabited: Inhabited[A], proposition: WeakProposition[A]) {
  /**
    * All inhabited subtypes of a contractible type are equal.
    */
  def contract[B](implicit p: B <~< A, B: Inhabited[B]): B === A =
    proposition.equal[B, A](InhabitedSubset(p, B), InhabitedSubset(As.refl[A], inhabited))
}
object Contractible {
  def apply[A](implicit A: Contractible[A]): Contractible[A] = A

  implicit def witness[A](implicit inhabited: Inhabited[A], proposition: WeakProposition[A]): Contractible[A] =
    Contractible[A](inhabited, proposition)

  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Contractible[A] =
    new Contractible[A](Inhabited.value(A.value), Proposition.singleton[A])
}