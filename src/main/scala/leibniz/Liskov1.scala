package leibniz

import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

sealed abstract class Liskov1[-L, +H >: L, A >: L <: H, B >: L <: H] { ab =>
  type Lower >: L <: Upper
  type Upper >: L <: H

  def lower: Leibniz[L, H, A, Lower]
  def upper: Leibniz[L, H, B, Upper]

  def weaken: Liskov[L, H, A, B] = {
    type f[x >: L <: H, y >: L <: H] = Liskov[L, H, x, y]
    Leibniz.pair(lower.flip, upper.flip).subst[f](
      Liskov.reify[L, H, Lower, Upper])
  }

  def strengthen: Liskov2[L, H, A, B] =
    weaken.strengthenTwice[L, H, A, B]

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
  (bc: Liskov1[L2, H2, B, C]): Liskov1[L2, H2, A, C] =
    Liskov1.compose[L2, H2, A, B, C](bc, ab)

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[L2 <: L, H2 >: H, Z >: L2 <: H2]
  (za: Liskov1[L2, H2, Z, A]): Liskov1[L2, H2, Z, B] =
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
    * Given `Liskov1[L, H, A, B]`, prove `A <~< B`.
    */
  final def toAs: A <~< B = {
    type f[+a] = A <~< a
    substCo[f](As.refl[A])
  }
}
object Liskov1 {
  final case class Refl[A]() extends Liskov1[A, A, A, A] {
    type Lower = A
    type Upper = A
    def lower: Leibniz[A, A, A, A] = Leibniz.refl[A]
    def upper: Leibniz[A, A, A, A] = Leibniz.refl[A]
  }

  implicit def proposition[L, H >: L, A >: L <: H, B >: L <: H]: Proposition[Liskov1[L, H, A, B]] =
    Liskov.proposition[L, H, A, B].isomap(Iso.unsafe(_.strengthen, _.weaken))

  def apply[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov[L, H, A, B] = ab

  /**
    * Subtyping relation is reflexive.
    */
  def refl[A]: Liskov1[A, A, A, A] = Refl[A]()

  def proved[
  L, H >: L,
  A >: L <: H, B >: L <: H,
  A1 >: L <: B1,
  B1 >: L <: H
  ](a: Leibniz[L, H, A, A1], b: Leibniz[L, H, B, B1]): Liskov1[L, H, A, B] =
    new Liskov1[L, H, A, B] {
      type Upper = B1
      type Lower = A1
      def lower: Leibniz[L, H, A, A1] = a
      def upper: Leibniz[L, H, B, B1] = b
    }

  implicit def fix[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov1[L, H, A, B] = ab.strengthen[L, H, A, B]

  /**
    * Reify Scala's subtyping relationship into an evidence value.
    */
  def reify[L, H >: L, A >: L <: (H with B), B >: L <: H]: Liskov1[L, H, A, B] =
    Liskov.reify[L, H, A, B].strengthen[L, H, A, B]

  /**
    * Subtyping is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[Liskov1.compose]]
    * @see [[Liskov1.andThen]]
    */
  def compose[L, H >: L, A >: L <: H, B >: L <: H, C >: L <: H]
  (bc: Liskov1[L, H, B, C], ab: Liskov1[L, H, A, B]): Liskov1[L, H, A, C] = {
    type f[+x >: L <: H] = Liskov[L, H, A, x]
    bc.substCo[f](ab.weaken).strengthen
  }

  /**
    * Subtyping is antisymmetric in theory (and in Dotty). Notice that this is
    * not true in Scala until [[https://issues.scala-lang.org/browse/SI-7278
    * SI-7278]] is fixed, so this function is marked unsafe.
    */
  def bracket[L, H >: L, A >: L <: H, B >: L <: H]
  (f: Liskov1[L, H, A, B], g: Liskov1[L, H, B, A])(implicit unsafe: Unsafe): Leibniz[L, H, A, B] =
    Leibniz.fromIs[L, H, A, B](As.bracket(f.toAs, g.toAs))

  /**
    * It can be convenient to convert a [[<:<]] value into a `<~<` value.
    * This is not strictly valid as while it is almost certainly true that
    * `A <:< B` implies `A <~< B` it is not the case that you can create
    * evidence of `A <~< B` except via a coercion. Use responsibly.
    */
  def fromPredef[L, H >: L, A >: L <: H, B >: L <: H](eq: A <:< B): Liskov1[L, H, A, B] =
    fromAs[L, H, A, B](As.fromPredef(eq))

  /**
    * Given `A <~< B` with `A >: L <: H` and `B >: L <: H`,
    * prove `Liskov[L, H, A, B]`.
    */
  def fromAs[L, H >: L, A >: L <: H, B >: L <: H](eq: A <~< B): Liskov1[L, H, A, B] = {
    val A1B1 = eq.fix[A, B]

    val A2: Squash[Nothing, A1B1.Upper, A1B1.Lower, L, H, A] =
      Axioms.squash[Nothing, A1B1.Upper, A1B1.Lower, L, H, A](A1B1.lower.flip)
    val B2: Squash[L, H, B, A2.Type, A1B1.Upper, A1B1.Upper] =
      Axioms.squash[L, H, B, A2.Type, A1B1.Upper, A1B1.Upper](A1B1.upper)

    val eqA_A2: A === A2.Type = A1B1.lower andThen A2.left
    val eqB_B2: B === B2.Type = B2.left

    proved[L, H, A, B, A2.Type, B2.Type](
      Leibniz.fromIs[L, H, A, A2.Type](eqA_A2),
      Leibniz.fromIs[L, H, B, B2.Type](eqB_B2))
  }
}