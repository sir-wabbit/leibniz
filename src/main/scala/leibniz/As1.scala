package leibniz

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
  private[this] final case class Refl[A]() extends As1[A, A] {
    type Lower = A
    type Upper = A
    def lower = Is.refl[A]
    def upper = Is.refl[A]
  }

  def refl[A]: A As1 A = new Refl[A]()

  def proved[A, B, B1 >: A, A1 <: (B with B1)](a: A Is A1, b: B Is B1): As1[A, B] = new As1[A, B] {
    type Upper = B1
    type Lower = A1
    def lower: A Is Lower = a
    def upper: B Is Upper = b
  }
}