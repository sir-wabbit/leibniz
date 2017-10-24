package leibniz

import leibniz.inhabitance.Proposition
import leibniz.variance.{Contravariant, Covariant}

/**
  * Liskov substitutability: A better `<:<`.
  *
  * `Liskov[A, B]` witnesses that `A` can be used in any negative context
  * that expects a `B`. (e.g. if you could pass an `A` into any function
  * that expects a `B`.)
  *
  * @see [[<~<]] `A <~< B` is a type synonym to `Liskov[A, B]`
  */
sealed abstract class Liskov[-L, +H >: L, -A >: L <: H, +B >: L <: H] private[Liskov]() { ab =>
  def fix[L1 <: L, H1 >: H, A1 >: L1 <: A, B1 >: B <: H1]: Liskov1[L1, H1, A1, B1]

  /**
    * Substitution into a covariant context.
    *
    * @see [[substCt]]
    */
  def substCo[F[+_ >: L <: H]](fa: F[A]): F[B]

  /**
    * Substitution into a contravariant context.
    *
    * @see [[substCo]]
    */
  def substCt[F[-_ >: L <: H]](fb: F[B]): F[A]


  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    *
    * @see [[coerce]]
    */
  final def apply(a: A): B =
    coerce(a)

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    */
  final def andThen[L2 <: L, H2 >: H, C >: L2 <: H2]
  (bc: Liskov[L2, H2, B, C]): Liskov[L2, H2, A, C] =
    Liskov.compose[L2, H2, A, B, C](bc, ab)

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[L2 <: L, H2 >: H, Z >: L2 <: H2]
  (za: Liskov[L2, H2, Z, A]): Liskov[L2, H2, Z, B] =
    za.andThen(ab)

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    *
    * @see [[apply]]
    */
  final def coerce(a: A): B = {
    type f[+a] = a
    substCo[f](a)
  }

  /**
    * Given `Liskov[L, H, A, B]`, prove `A <:< B`.
    */
  final def toPredef: A <:< B = {
    type f[+a] = A <:< a
    substCo[f](implicitly[A <:< A])
  }

  /**
    * Given `Liskov[L, H, A, B]`, prove `A <~< B`.
    */
  final def toAs: A <~< B = {
    type f[+a] = A <~< a
    substCo[f](implicitly[A <~< A])
  }
}

object Liskov {
  implicit def proposition[L, H >: L, A >: L <: H, B >: L <: H]: Proposition[Liskov[L, H, A, B]] = {
    import leibniz.Unsafe._
    Proposition.force[Liskov[L, H, A, B]]
  }

  def apply[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov[L, H, A, B] = ab

  final case class Refl[A]() extends Liskov[A, A, A, A] {
    def fix[L1 <: A, H1 >: A, A1 >: L1 <: A, B1 >: A <: H1]: Liskov1[L1, H1, A1, B1] =
      Liskov1.proved[L1, H1, A1, B1, A1, B1](Leibniz.refl[A1], Leibniz.refl[B1])

    // Technically, `fix` is enough to implement `substCo` and `substCt`,
    // but it seems like a good idea to keep all three.
    // NOTE: `substCo` or `substCt` is not enough to implement `fix`.
    def substCo[F[+_ >: A <: A]](fa: F[A]): F[A] = fa
    def substCt[F[-_ >: A <: A]](fa: F[A]): F[A] = fa
  }

  /**
    * Unsafe coercion between types. `unsafeForce` abuses `asInstanceOf` to
    * explicitly coerce types. It is unsafe.
    */
  def force[L, H >: L, A >: L <: H, B >: L <: H](implicit unsafe: Unsafe): Liskov[L, H, A, B] =
    unsafe.coerceK0[Liskov[L, H, A, B]](refl[Any])

  /**
    * Subtyping relation is reflexive.
    */
  implicit def refl[A]: Liskov[A, A, A, A] = Refl[A]()

  /**
    * Reify Scala's subtyping relationship into an evidence value.
    */
  implicit def reify[
    L, H >: L,
    A >: L <: (H with B),
    B >: L <: H
  ]: Liskov[L, H, A, B] = refl[A]

  /**
    * Subtyping is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[Liskov1.compose]]
    * @see [[Liskov1.andThen]]
    */
  def compose[L, H >: L, A >: L <: H, B >: L <: H, C >: L <: H]
  (bc: Liskov[L, H, B, C], ab: Liskov[L, H, A, B]): Liskov[L, H, A, C] =
    bc.substCo[λ[`+α >: L <: H` => Liskov[L, H, A, α]]](ab)

  /**
    * Subtyping is antisymmetric in theory (and in Dotty). Notice that this is
    * not true in Scala until [[https://issues.scala-lang.org/browse/SI-7278
    * SI-7278]] is fixed, so this function is marked unsafe.
    */
  def bracket[L, H >: L, A >: L <: H, B >: L <: H]
  (f: Liskov[L, H, A, B], g: Liskov[L, H, B, A])(implicit unsafe: Unsafe): Leibniz[L, H, A, B] =
    Leibniz.force[L, H, A, B]

  /**
    * Given `A <:< B` with `A >: L <: H` and `B >: L <: H`,
    * prove `Liskov[L, H, A, B]`.
    */
  def fromPredef[L, H >: L, A >: L <: H, B >: L <: H](eq: A <:< B): Liskov[L, H, A, B] = {
    import Unsafe._
    force[L, H, A, B]
  }

  /**
    * Given `A <~< B` with `A >: L <: H` and `B >: L <: H`,
    * prove `Liskov[L, H, A, B]`.
    */
  def fromAs[L, H >: L, A >: L <: H, B >: L <: H](eq: A <~< B): Liskov[L, H, A, B] = {
    import Unsafe._
    force[L, H, A, B]
  }

  implicit class liskovSyntax[L, H >: L, A >: L <: H, B >: L <: H]
  (val ab: Liskov[L, H, A, B]) extends AnyVal
  {
    import Unsafe._

    def liftCoF[LF, HF >: LF, F[_] >: LF <: HF]
    (implicit F: Covariant[F]): Liskov[LF, HF, F[A], F[B]] =
      force[LF, HF, F[A], F[B]]

    def liftCtF[LF, HF >: LF, F[_] >: LF <: HF]
    (implicit F: Contravariant[F]): Liskov[LF, HF, F[B], F[A]] =
      force[LF, HF, F[B], F[A]]

    def substCoF[LF, HF >: LF, F[_] >: LF <: HF]
    (fa: F[A])(implicit F: Covariant[F]): F[B] =
      liftCoF[LF, HF, F].coerce(fa)

    def substCt[LF, HF >: LF, F[_] >: LF <: HF]
    (fb: F[B])(implicit F: Contravariant[F]): F[A] =
      liftCtF[LF, HF, F].coerce(fb)
  }
}