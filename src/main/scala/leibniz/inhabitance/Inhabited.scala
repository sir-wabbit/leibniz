package leibniz.inhabitance

import leibniz.internal.Unsafe
import leibniz.{<~<, Void}

/**
  * Witnesses that [[A]] is inhabited.
  */
sealed abstract class Inhabited[+A] {
  import Inhabited._

  def contradicts(f: A => Void): Void

  def widen[B](implicit p: A <~< B): Inhabited[B] =
    p.substCo[Inhabited](this)

  def map[B](f: A => B): Inhabited[B] =
    witness[B](k => contradicts(a => k(f(a))))
}
object Inhabited {
  private[this] final class Witness[A](a: (A => Void) => Void) extends Inhabited[A] {
    def contradicts(f: A => Void): Void = a(f)
  }

  def apply[A](implicit A: Inhabited[A]): Inhabited[A] = A

  def witness[A](a: (A => Void) => Void): Inhabited[A] =
    new Witness[A](a)

  def value[A](a: A): Inhabited[A] =
    witness[A](f => f(a))

  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Inhabited[A] =
    witness(f => f(A.value))

  implicit def inhabited[A](implicit A: Inhabited[A]): Inhabited[Inhabited[A]] =
    witness(f => f(A))

  implicit def uninhabited[A](implicit na: Uninhabited[A]): Uninhabited[Inhabited[A]] =
    Uninhabited.witness(A => A.contradicts(a => na.contradicts(a)))

  implicit def proposition[A]: Proposition[Inhabited[A]] =
    Proposition.force[Inhabited[A]](Unsafe.unsafe)

  implicit def contractible[A](implicit A: Inhabited[A]): Contractible[Inhabited[A]] =
    Contractible.witness[Inhabited[A]](inhabited, proposition[A])
}