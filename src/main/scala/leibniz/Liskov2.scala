package leibniz

import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

sealed abstract class Liskov2[-L, +H >: L, A >: L <: H, B >: L <: H] { ab =>
  type Lower >: L <: (B with Upper)
  type Upper >: A <: H

  def lower: Leibniz[L, H, A, Lower]
  def upper: Leibniz[L, H, B, Upper]

  def weakenTwice: Liskov[L, H, A, B] = {
    type f[x >: L <: H, y >: L <: H] = Liskov[L, H, x, y]
    Leibniz.pair(lower.flip, upper.flip).subst[f](
      Liskov.reify[L, H, Lower, Upper])
  }

  def weaken: Liskov1[L, H, A, B] =
    Liskov1.proved[L, H, A, B, Lower, Upper](lower, upper)

  def substCt[F[-_ >: L <: H]](fb: F[B]): F[A] =
    lower.flip.subst[F](upper.subst[F](fb) : F[Lower])

  def substCo[F[+_ >: L <: H]](fa: F[A]): F[B] =
    upper.flip.subst[F](lower.subst[F](fa) : F[Upper])

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    */
  def coerce(a: A): B = {
    type f[+x >: L <: H] = x
    substCo[f](a)
  }

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    */
  final def andThen[L2 <: L, H2 >: H, C >: L2 <: H2]
  (bc: Liskov2[L2, H2, B, C]): Liskov2[L2, H2, A, C] =
    Liskov2.compose[L2, H2, A, B, C](bc, ab)

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[L2 <: L, H2 >: H, Z >: L2 <: H2]
  (za: Liskov2[L2, H2, Z, A]): Liskov2[L2, H2, Z, B] =
    za.andThen(ab)

  /**
    * A value of `A <~< B` is always sufficient to produce a similar [[<:<]]
    * value.
    */
  final def toPredef: A <:< B = {
    type f[-α] = α <:< B
    substCt[f](implicitly[B <:< B])
  }

  /**
    * Given `Liskov2[L, H, A, B]`, prove `A <~< B`.
    */
  final def toAs: A <~< B = {
    type f[+a] = A <~< a
    substCo[f](As.refl[A])
  }
}
object Liskov2 {
  final case class Refl[A]() extends Liskov2[A, A, A, A] {
    type Lower = A
    type Upper = A
    def lower: Leibniz[A, A, A, A] = Leibniz.refl[A]
    def upper: Leibniz[A, A, A, A] = Leibniz.refl[A]
  }

  implicit def proposition[L, H >: L, A >: L <: H, B >: L <: H]: Proposition[Liskov2[L, H, A, B]] =
    Proposition.force[Liskov2[L, H, A, B]](Unsafe.unsafe)

  def apply[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov[L, H, A, B] = ab

  /**
    * Subtyping relation is reflexive.
    */
  def refl[A]: Liskov2[A, A, A, A] = Refl[A]()

  def proved[
    L, H >: L,
    A >: L <: H, B >: L <: H,
    A1 >: L <: (B with B1),
    B1 >: A <: H
  ](a: Leibniz[L, H, A, A1], b: Leibniz[L, H, B, B1]): Liskov2[L, H, A, B] =
    new Liskov2[L, H, A, B] {
      type Upper = B1
      type Lower = A1
      def lower: Leibniz[L, H, A, A1] = a
      def upper: Leibniz[L, H, B, B1] = b
    }

  implicit def fix[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov2[L, H, A, B] = ab.strengthenTwice[L, H, A, B]

  /**
    * Reify Scala's subtyping relationship into an evidence value.
    */
  def reify[L, H >: L, A >: L <: (H with B), B >: L <: H]: Liskov2[L, H, A, B] =
    Liskov.reify[L, H, A, B].strengthenTwice[L, H, A, B]

  /**
    * Subtyping is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[Liskov2.compose]]
    * @see [[Liskov2.andThen]]
    */
  def compose[L, H >: L, A >: L <: H, B >: L <: H, C >: L <: H]
  (bc: Liskov2[L, H, B, C], ab: Liskov2[L, H, A, B]): Liskov2[L, H, A, C] = {
    type f[+x >: L <: H] = Liskov[L, H, A, x]
    bc.substCo[f](ab.weakenTwice).strengthenTwice
  }

  /**
    * Subtyping is antisymmetric in theory (and in Dotty). Notice that this is
    * not true in Scala until [[https://issues.scala-lang.org/browse/SI-7278
    * SI-7278]] is fixed, so this function is marked unsafe.
    */
  def bracket[L, H >: L, A >: L <: H, B >: L <: H]
  (f: Liskov2[L, H, A, B], g: Liskov2[L, H, B, A])(implicit unsafe: Unsafe): Leibniz[L, H, A, B] =
    Leibniz.fromIs[L, H, A, B](As.bracket(f.toAs, g.toAs))

  /**
    * It can be convenient to convert a [[<:<]] value into a `<~<` value.
    * This is not strictly valid as while it is almost certainly true that
    * `A <:< B` implies `A <~< B` it is not the case that you can create
    * evidence of `A <~< B` except via a coercion. Use responsibly.
    */
  def fromPredef[L, H >: L, A >: L <: H, B >: L <: H](eq: A <:< B): Liskov2[L, H, A, B] =
    Liskov.fromPredef[L, H, A, B](eq).strengthenTwice[L, H, A, B]

  /**
    * Given `A <~< B` with `A >: L <: H` and `B >: L <: H`,
    * prove `Liskov[L, H, A, B]`.
    */
  def fromAs[L, H >: L, A >: L <: H, B >: L <: H](eq: A <~< B): Liskov2[L, H, A, B] =
    Liskov.fromAs[L, H, A, B](eq).strengthenTwice[L, H, A, B]

  /**
    * Unsafe coercion between types. `unsafeForce` abuses `asInstanceOf` to
    * explicitly coerce types. It is unsafe.
    */
  def force[L, H >: L, A >: L <: H, B >: L <: H](implicit unsafe: Unsafe): Liskov2[L, H, A, B] =
    unsafe.coerceK0[Liskov2[L, H, A, B]](refl[Any])
}