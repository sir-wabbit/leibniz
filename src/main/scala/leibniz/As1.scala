package leibniz

import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe
import leibniz.variance.{Contravariant, Covariant}

sealed abstract class As1[A, B] { ab =>
  type Upper >: A
  type Lower <: (B with Upper)

  def lower: A === Lower
  def upper: B === Upper

  def loosen: A <~< B = {
    type f1[x] = x <~< Upper
    type f2[x] = A <~< x

    upper.flip.subst[f2](
      lower.flip.subst[f1](
        As.refl[Lower] : Lower <~< Upper))
  }

  def substCt[F[-_]](fb: F[B]): F[A] =
    lower.flip.subst[F](upper.subst[F](fb) : F[Lower])

  def substCo[F[+_]](fa: F[A]): F[B] =
    upper.flip.subst[F](lower.subst[F](fa) : F[Upper])

  def coerce(a: A): B = {
    type f[+x] = x
    substCo[f](a)
  }

  def liftCoF[F[_]](implicit F: Covariant[F]): F[A] As1 F[B] =
    F.lift(ab.loosen).fix

  def liftCtF[F[_]](implicit F: Contravariant[F]): F[B] As1 F[A] =
    F.lift(ab.loosen).fix

  def substCoF[F[_]](fa: F[A])(implicit F: Covariant[F]): F[B] =
    liftCoF[F].coerce(fa)

  def substCtF[F[_]](fb: F[B])(implicit F: Contravariant[F]): F[A] =
    liftCtF[F].coerce(fb)
}
object As1 {
  private[this] final case class Refl[A]() extends As1[A, A] {
    type Lower = A
    type Upper = A
    def lower: A === A = Is.refl[A]
    def upper: A === A = Is.refl[A]
  }

  implicit def proposition[A, B]: Proposition[As1[A, B]] =
    Proposition.force[As1[A, B]](Unsafe.unsafe)

  def apply[A, B](implicit ev: A As1 B): A As1 B = ev

  def refl[A]: A As1 A = new Refl[A]()

  def force[A, B](implicit unsafe: Unsafe): A As1 B =
    As.force[A, B].fix[A, B]

  implicit def fix[A, B](implicit ab: A <~< B): A As1 B = ab.fix[A, B]

  def proved[A, B, B1 >: A, A1 <: (B with B1)](a: A Is A1, b: B Is B1): As1[A, B] = new As1[A, B] {
    type Upper = B1
    type Lower = A1
    def lower: A Is Lower = a
    def upper: B Is Upper = b
  }


}