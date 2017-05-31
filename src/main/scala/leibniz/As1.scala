package leibniz

import cats.Functor
import cats.functor.Contravariant

sealed abstract class As1[A, B] {
  type Upper >: A
  type Lower <: (B with Upper)
  def lower: A Is Lower
  def upper: B Is Upper

  def loosen: A As B = {
    type f1[x] = x As Upper
    type f2[x] = A As x

    upper.flip.subst[f2](
      lower.flip.subst[f1](
        As.refl[Lower] : Lower As Upper))
  }

  def substCt[F[-_]](fb: F[B]): F[A] =
    lower.flip.subst[F](upper.subst[F](fb) : F[Lower])

  def substCo[F[+_]](fa: F[A]): F[B] =
    upper.flip.subst[F](lower.subst[F](fa) : F[Upper])

  def coerce(a: A): B = {
    type f[+x] = x
    substCo[f](a)
  }
}
object As1 {
  final case class Refl[A]() extends As1[A, A] {
    type Lower = A
    type Upper = A
    def lower: Is[A, A] = Is.refl[A]
    def upper: Is[A, A] = Is.refl[A]
  }

  def refl[A]: A As1 A = new Refl[A]()

  def unsafeForce[A, B]: A As1 B =
    As.unsafeForce[A, B].fix[A, B]

  implicit def fix[A, B](implicit ab: A As B): A As1 B = ab.fix[A, B]

  def proved[A, B, B1 >: A, A1 <: (B with B1)](a: A Is A1, b: B Is B1): As1[A, B] = new As1[A, B] {
    type Upper = B1
    type Lower = A1
    def lower: A Is Lower = a
    def upper: B Is Upper = b
  }

  implicit class As1Ops[A, B](val ab: As1[A, B]) extends AnyVal {
    // HACK: This is ridiculously hacky.
    import hacks._
    final def toLiskov[L <: (A with B), H >: ~[~[A] with ~[B]]]: Liskov[L, H, ~[A], ~[B]] =
      Liskov.unsafeForce[L, H, ~[A], ~[B]]

    def liftCoF[F[_]](implicit F: Functor[F]): F[A] As1 F[B] =
      unsafeForce[F[A], F[B]]

    def liftCtF[F[_]](implicit F: Contravariant[F]): F[B] As1 F[A] =
      unsafeForce[F[B], F[A]]

    def substCoF[F[_]](fa: F[A])(implicit F: Functor[F]): F[B] =
      liftCoF[F].coerce(fa)

    def substCtF[F[_]](fb: F[B])(implicit F: Contravariant[F]): F[A] =
      liftCtF[F].coerce(fb)
  }
}