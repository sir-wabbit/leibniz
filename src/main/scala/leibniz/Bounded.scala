package leibniz

import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

sealed abstract class Bounded[-L, +U >: L, A] private [Bounded] () {
  type Type >: L <: U
  def proof: A === Type
}
object Bounded {
  implicit def proposition[L, U >: L, A]: Proposition[Bounded[L, U, A]] =
    Proposition.force[Bounded[L, U, A]](Unsafe.unsafe)

  def apply[L, U >: L, A](implicit ev: Bounded[L, U, A]): Bounded[L, U, A] = ev

  final case class Refl[A]() extends Bounded[A, A, A] {
    type Type = A
    val proof: A === A = Is.refl
  }

  implicit def refl[A]: Bounded[A, A, A] = Refl[A]()

  implicit def reify[L, U >: L, A >: L <: U]: Bounded[L, U, A] = refl[A]
}