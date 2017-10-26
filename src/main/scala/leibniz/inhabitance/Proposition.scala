package leibniz.inhabitance

import leibniz._
import leibniz.internal.Unsafe

/**
  * Witnesses that all values (a: A) are equal.
  *
  * @see [[https://ncatlab.org/nlab/show/mere+proposition]]
  */
sealed abstract class Proposition[A] { prop =>
  def equal[B, C](implicit b: B <~< A, c: C <~< A, B: Inhabited[B], C: Inhabited[C]): B === C

  def contractible(implicit A: Inhabited[A]): Contractible[A] =
    Contractible.construct[A](A, this)
}
object Proposition {
  private[this] final class Forced[A](implicit unsafe: Unsafe) extends Proposition[A] {
    def equal[B, C](implicit b: B <~< A, c: C <~< A, B: Inhabited[B], C: Inhabited[C]): B === C =
      Is.force[B, C]
  }

  def apply[A](implicit A: Proposition[A]): Proposition[A] = A

  implicit def eq[A](implicit prop: Proposition[A]): Eq[A] = Eq.propositionEq[A]

  implicit def prop[A](implicit prop: Proposition[A]): Proposition[Proposition[A]] =
    force[Proposition[A]](Unsafe.unsafe)

  implicit def singleton[A <: Singleton]: Proposition[A] =
    force[A](Unsafe.unsafe)

  def force[A](implicit unsafe: Unsafe): Proposition[A] =
    new Forced[A]
}
