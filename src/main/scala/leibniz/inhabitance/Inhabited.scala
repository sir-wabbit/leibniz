package leibniz
package inhabitance

import leibniz.internal.Unsafe
import leibniz.{<~<, Void}

/**
  * Witnesses that [[A]] is inhabited.
  */
sealed abstract class Inhabited[A] { a =>
  import Inhabited._

  def contradicts(f: A => Void): Void

  def widen[B](implicit p: A <~< B): Inhabited[B]

  def map[B](f: A => B): Inhabited[B] =
    witness[B](k => a.contradicts(a => k(f(a))))

  def flatMap[B](f: A => Inhabited[B]) =
    witness[B](k => a.contradicts(a => f(a).contradicts(k)))

  def zip[B](b: Inhabited[B]): Inhabited[(A, B)] =
    flatMap(a => b.flatMap(b => Inhabited.value((a, b))))
}
trait InhabitedLowerPriority {
  implicit def mkInhabited[A]: Inhabited[A] =
    macro internal.MacroUtil.mkInhabited[A]
}
object Inhabited extends InhabitedLowerPriority {
  private[this] final class Witness[+A](a: (A => Void) => Void) extends Inhabited[A] {
    def contradicts(f: A => Void): Void = a(f)

    def widen[B](implicit p: A <~< B): Inhabited[B] =
      p.substCo[Witness](this)
  }

  def apply[A](implicit A: Inhabited[A]): Inhabited[A] = A

  def witness[A](a: (A => Void) => Void): Inhabited[A] =
    new Witness[A](a)

  def value[A](a: A): Inhabited[A] =
    witness[A](f => f(a))

  def map2[A, B, C](f: (A, B) => C)(implicit A: Inhabited[A], B: Inhabited[B]): Inhabited[C] =
    for { a <- A; b <- B } yield f(a, b)

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

  def lem[A]: Inhabited[Either[A => Void, A]] =
    witness(k => k(Left(a => k(Right(a)))))

  def and[A, B](f: (A, B) => Void): Inhabited[Either[A => Void, B => Void]] =
    witness(p => p(Right(b => p(Left(a => f(a, b))))))

  def imp[A, B](f: A => B): Inhabited[Either[A => Void, B]] =
    witness(k => k(Left(a => k(Right(f(a))))))

  def pierce[A]: Inhabited[((A => Void) => A) => A] =
    witness(k => k((p: (A => Void) => A) => p((a: A) => k(_ => a))))
}