package leibniz.inhabitance

import leibniz.internal.Unsafe
import leibniz.{<~<, Void}

/**
  * Witnesses that [[A]] is inhabited.
  */
sealed abstract class Inhabited[+A] {
  def contradicts(f: A => Void): Void

  def widen[B](implicit p: A <~< B): Inhabited[B] =
    p.substCo[Inhabited](this)
}
object Inhabited {
  private[leibniz] final class Single[A](a: A) extends Inhabited[A] {
    def contradicts(f: A => Void): Void = f(a)
  }

  def apply[A](implicit A: Inhabited[A]): Inhabited[A] = A

  def witness[A](a: A): Inhabited[A] =
    new Single[A](a)

  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Inhabited[A] =
    new Single[A](valueOf[A])

  implicit def inhabited[A](implicit A: Inhabited[A]): Inhabited[Inhabited[A]] =
    witness(A)

  implicit def uninhabited[A](implicit na: Uninhabited[A]): Uninhabited[Inhabited[A]] =
    Uninhabited.witness(A => A.contradicts(a => na.contradicts(a)))

  implicit def proposition[A]: Proposition[Inhabited[A]] =
    Proposition.force[Inhabited[A]](Unsafe.unsafe)

  implicit def contractible[A](implicit A: Inhabited[A]): Contractible[Inhabited[A]] =
    Contractible.construct[Inhabited[A]](inhabited, proposition[A])
}