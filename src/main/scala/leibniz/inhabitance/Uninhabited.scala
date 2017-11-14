package leibniz.inhabitance

import leibniz.internal.Unsafe
import leibniz.{<~<, ===, Void}

sealed abstract class Uninhabited[-A] { notA =>
  import Uninhabited._

  def contradicts(a: A): Void

  def narrow[B](implicit p: B <~< A): Uninhabited[B] =
    p.substCt[Uninhabited](this)

  def contramap[B](f: B => A): Uninhabited[B] =
    witness[B](b => contradicts(f(b)))

  def zip[B](notB: Uninhabited[B]): Uninhabited[Either[A, B]] =
    witness[Either[A, B]] {
      case Left(a) => notA.contradicts(a)
      case Right(b) => notB.contradicts(b)
    }
}
object Uninhabited {
  private[this] final class Witness[A](f: A => Void) extends Uninhabited[A] {
    def contradicts(a: A): Void = f(a)
  }

  def apply[A](implicit ev: Uninhabited[A]): Uninhabited[A] = ev

  def witness[A](f: A => Void): Uninhabited[A] =
    new Witness[A](f)

  def contramap2[A, B, C](p: Inhabited[Either[Uninhabited[A], Uninhabited[B]]])(f: C => (A, B)): Uninhabited[C] =
    witness { c =>
      val (a, b) = f(c)
      p.contradicts {
        case Left(notA) => notA.contradicts(a)
        case Right(notB) => notB.contradicts(b)
      }
    }

  def codivide[A, B, C](p: Inhabited[(Uninhabited[A], Uninhabited[B])])(f: C => Either[A, B]): Uninhabited[C] =
    witness { c =>
      p.contradicts { case (notA, notB) =>
        f(c) match {
          case Left(a) => notA.contradicts(a)
          case Right(b) => notB.contradicts(b)
        }
      }
    }

  implicit def inhabited[A](implicit A: Uninhabited[A]): Inhabited[Uninhabited[A]] =
    Inhabited.witness(f => f(A))

  implicit def uninhabited[A](implicit A: Inhabited[A]): Uninhabited[Uninhabited[A]] =
    Uninhabited.witness(nA => A.contradicts(a => nA.contradicts(a)))

  implicit def proposition[A]: Proposition[Uninhabited[A]] =
    Proposition.force[Uninhabited[A]](Unsafe.unsafe)
}