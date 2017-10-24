package leibniz.inhabitance

import leibniz._

/**
  * Witnesses that all values (a: A) are equal.
  *
  * @see [[https://ncatlab.org/nlab/show/mere+proposition]]
  */
trait Proposition[A] { prop =>
  def equal[B, C](implicit b: B <~< A, c: C <~< A, B: Inhabited[B], C: Inhabited[C]): B === C

  def contractible(implicit A: Inhabited[A]): Contractible[A] =
    Contractible.construct[A](A, this)
}
object Proposition {
  private[this] final class Forced[A](implicit unsafe: Unsafe) extends Proposition[A] {
    def equal[B, C](implicit b: B <~< A, c: C <~< A, B: Inhabited[B], C: Inhabited[C]): B === C =
      Is.force[B, C]
  }

  implicit def eq[A](implicit prop: Proposition[A]): Eq[A] = Eq.propositionEq[A]

  def force[A](implicit unsafe: Unsafe): Proposition[A] =
    new Forced[A]

  implicit def prop[A](implicit prop: Proposition[A]): Proposition[Proposition[A]] = {
    import Unsafe._
    force[Proposition[A]]
  }

  implicit def singleton[A <: Singleton]: Proposition[A] = {
    import Unsafe._
    force[A]
  }

  def classically[A](proof: (A => Void) => Void)(implicit prop: Proposition[A]): A = {
    import Unsafe._
    unsafe.cps(proof)
  }
}
