package leibniz
package inhabitance

import leibniz.macros.newtype
import leibniz.variance.Contravariant

@newtype final case class Uninhabited[A](run: A => Void) { notA =>
  import Uninhabited._

  def contradicts(a: A): Void = run(a)

  def notInhabited(a: Inhabited[A]): Void =
    a.contradicts(contradicts)

  def contramap[B](f: B => A): Uninhabited[B] =
    witness[B](b => contradicts(f(b)))

  def zip[B](notB: Uninhabited[B]): Uninhabited[Either[A, B]] =
    witness[Either[A, B]] {
      case Left(a) => notA.contradicts(a)
      case Right(b) => notB.contradicts(b)
    }
}

trait UninhabitedLowerPriority {
  implicit def mkUninhabited[A]: Uninhabited[A] =
    macro internal.MacroUtil.mkUninhabited[A]
}

object Uninhabited extends UninhabitedLowerPriority {
  def apply[A](implicit ev: Uninhabited[A]): Uninhabited[A] = ev

  def witness[A](f: A => Void): Uninhabited[A] = Uninhabited(f)

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
    Uninhabited.witness(nA => A.notUninhabited(nA))

  implicit def func[A, B](implicit A: Inhabited[A], B: Uninhabited[B]): Uninhabited[A => B] =
    Uninhabited.witness(f => A.notUninhabited(B.contramap(f)))

  implicit def proposition[A]: Proposition[Uninhabited[A]] =
    (nnA: ¬¬[Uninhabited[A]]) => new Uninhabited[A](a => nnA.contradicts(A => A.contradicts(a)))
}