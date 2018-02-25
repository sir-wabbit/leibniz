package leibniz

import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe
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
  def strengthenTwice[L1 <: L, H1 >: H, A1 >: L1 <: A, B1 >: B <: H1]: Liskov2[L1, H1, A1, B1]

  def strengthen[L1 <: L, H1 >: H, A1 >: L1 <: A, B1 >: B <: H1]: Liskov1[L1, H1, A1, B1] =
    strengthenTwice[L1, H1, A1, B1].weaken

  /**
    * Substitution into a covariant context.
    *
    * @see [[substCt]]
    */
  def substCo[F[+_ >: L <: H]](fa: F[A]): F[B] =
    strengthenTwice[L, H, A, B].substCo[F](fa)

  /**
    * Substitution into a contravariant context.
    *
    * @see [[substCo]]
    */
  def substCt[F[-_ >: L <: H]](fb: F[B]): F[A] =
    strengthenTwice[L, H, A, B].substCt[F](fb)

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
  implicit def proposition[L, H >: L, A >: L <: H, B >: L <: H]: Proposition[Liskov[L, H, A, B]] =
    (p: ¬¬[Liskov[L, H, A, B]]) => Axioms.liskovConsistency[L, H, A, B](p.run)

  def apply[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov[L, H, A, B] = ab

  final case class Refl[A]() extends Liskov[A, A, A, A] {
    def strengthenTwice[L1 <: A, H1 >: A, A1 >: L1 <: A, B1 >: A <: H1]: Liskov2[L1, H1, A1, B1] =
      Liskov2.proved[L1, H1, A1, B1, A1, B1](Leibniz.refl[A1], Leibniz.refl[B1])
  }

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
    * @see [[Liskov2.compose]]
    * @see [[Liskov2.andThen]]
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
    Leibniz.fromIs[L, H, A, B](As.bracket(f.toAs, g.toAs))

  implicit class liskovSyntax[L, H >: L, A >: L <: H, B >: L <: H]
  (val ab: Liskov[L, H, A, B]) extends AnyVal
  {
    def liftCoF[LF, HF >: LF, F[_] >: LF <: HF]
    (implicit F: Covariant[F]): Liskov[LF, HF, F[A], F[B]] =
      fromAs[LF, HF, F[A], F[B]](ab.toAs.liftCoF[F])

    def liftCtF[LF, HF >: LF, F[_] >: LF <: HF]
    (implicit F: Contravariant[F]): Liskov[LF, HF, F[B], F[A]] =
      fromAs[LF, HF, F[B], F[A]](ab.toAs.liftCtF[F])

    def substCoF[LF, HF >: LF, F[_] >: LF <: HF]
    (fa: F[A])(implicit F: Covariant[F]): F[B] =
      liftCoF[LF, HF, F].coerce(fa)

    def substCt[LF, HF >: LF, F[_] >: LF <: HF]
    (fb: F[B])(implicit F: Contravariant[F]): F[A] =
      liftCtF[LF, HF, F].coerce(fb)
  }

  /**
    * Given `A <:< B` with `A >: L <: H` and `B >: L <: H`,
    * prove `Liskov[L, H, A, B]`.
    */
  def fromPredef[L, H >: L, A >: L <: H, B >: L <: H](eq: A <:< B): Liskov[L, H, A, B] =
    fromAs(As.fromPredef(eq))

  /**
    * Given `A <~< B` with `A >: L <: H` and `B >: L <: H`,
    * prove `Liskov[L, H, A, B]`.
    */
  def fromAs[L, H >: L, A >: L <: H, B >: L <: H](eq: A <~< B): Liskov[L, H, A, B] =
    Liskov1.fromAs[L, H, A, B](eq).weaken
}