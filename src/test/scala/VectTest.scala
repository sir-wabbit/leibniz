package leibniz

import org.scalatest.{FunSuite, Matchers}
import Nat.{S, Z}
import leibniz.inhabitance.Uninhabited

class VectTest extends FunSuite with Matchers {
  sealed abstract class Vect[N, +A](implicit ev: N <:: Nat) {
    import Vect._

    def ::[B >: A](el: B): Vect[S[N], B] =
      new ::[N, B](el, this)

    def cata[F[_]](k: Vect.Cata[F, A]): F[N]
    def fold[F[_]](k: Vect.Fold[F, A]): F[N]

    def length: N = cata[λ[n => n]](new Vect.Cata[λ[n => n], A] {
      override def nil = Z
      override def cons[N](head: A, tail: N)(implicit ev: N <:: Nat) = S(tail)
    })

    def map[B](f: A => B): Vect[N, B] = cata[λ[n => Vect[n, B]]](new Vect.Cata[λ[n => Vect[n, B]], A] {
      override def nil = Nil
      override def cons[N](head: A, tail: Vect[N, B])(implicit ev: N <:: Nat): Vect[S[N], B] =
        f(head) :: tail
    })
  }
  object Vect {
    final case object Nil extends Vect[Z, Nothing] {
      def cata[F[_]](k: Vect.Cata[F, Nothing]): F[Z] = k.nil
      def fold[F[_]](k: Vect.Fold[F, Nothing]): F[Z] = k.nil
    }
    final case class ::[N, A](head: A, tail: Vect[N, A])(implicit ev: N <:: Nat) extends Vect[S[N], A] {
      def cata[F[_]](k: Vect.Cata[F, A]): F[S[N]] = k.cons[N](head, tail.cata[F](k))
      def fold[F[_]](k: Vect.Fold[F, A]): F[S[N]] = k.cons[N](head, tail)
    }

    trait Cata[F[_], -A] {
      def nil: F[Z]
      def cons[N](head: A, tail: F[N])(implicit ev: N <:: Nat): F[S[N]]
    }

    trait Fold[F[_], -A] {
      def nil: F[Z]
      def cons[N](head: A, tail: Vect[N, A])(implicit ev: N <:: Nat): F[S[N]]
    }
  }
  import Vect._

  def replicate[A](n: Nat, a: A): Vect[n.type, A] =
    n.cata[Vect[?, A]](new Nat.Cata[Vect[?, A]] {
      override def z: Vect[Z, A] = Vect.Nil
      override def s[M](n: Vect[M, A])(implicit p: M <:: Nat): Vect[S[M], A] = a :: n
    })

  test("vect-nat") {
    val two = S(S(Z))
    val v : Vect[two.type, Int] = replicate[Int](two, 1)
    println(replicate[Int](two, 1))
  }
}