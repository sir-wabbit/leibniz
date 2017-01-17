package leibniz

import leibniz.{ BoundedLeibniz => BL }

/**
  * This particular version of Leibnitz’ equality has been generalized to
  * handle subtyping so that it can be used with constrained type constructors
  * such as `F[_ <: X]`. `BoundedLeibniz[L, H, A, B]` says that `A` = `B`,
  * and that both of them are between `L` and `H`. Subtyping lets you loosen
  * the bounds on `L` and `H`.
  *
  * @see [[Leibniz]]
  */
sealed abstract class BoundedLeibniz[-L, +H >: L, A >: L <: H, B >: L <: H] private[BoundedLeibniz] () { ab =>
  /**
    * To create an instance of `Leibniz[A, B]` you must show that for every
    * choice of `F[_]` you can convert `F[A]` to `F[B]`.
    */
  def subst[F[_ >: L <: H]](fa: F[A]): F[B]

  /**
    * Substitution on identity brings about a direct coercion function of the
    * same form that `=:=` provides.
    *
    * @see [[coerce]]
    */
  final def apply(a: A): B =
    coerce(a)

  /**
    * Substitution on identity brings about a direct coercion function of the
    * same form that [[=:=]] provides.
    *
    * @see [[apply]]
    */
  final def coerce(a: A): B =
    subst[λ[α => α]](a)

  /**
    * Equality is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[compose]]
    */
  final def andThen[L2 <: L, H2 >: H, C >: L2 <: H2]
  (bc: BL[L2, H2, B, C]): BL[L2, H2, A, C] =
    BL.trans[L2, H2, A, B, C](bc, ab)

  /**
    * Equality is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[L2 <: L, H2 >: H, Z >: L2 <: H2]
  (za: BL[L2, H2, Z, A]): BL[L2, H2, Z, B] =
    BL.trans[L2, H2, Z, A, B](ab, za)

  /**
    * Equality is symmetric relation and therefore can be flipped around.
    * Flipping is its own inverse, so `x.flip.flip == x`.
    */
  final def flip: BL[L, H, B, A] =
    BL.symm(ab)

  /**
    * Given `A === B` we can prove that `F[A] === F[B]`.
    *
    * @see [[BoundedLeibniz.lift]]
    * @see [[BoundedLeibniz.lift2]]
    * @see [[BoundedLeibniz.lift3]]
    */
  final def lift[LF, HF >: LF, F[_ >: L <: H] >: LF <: HF]: BL[LF, HF, F[A], F[B]] =
    BL.lift[L, H, A, B, LF, HF, F](ab)

  final def onF[X](fa: X => A): X => B =
    subst[X => ?](fa)

  final def toUnbounded: Leibniz[A, B] =
    ab.subst[λ[α => Leibniz[A, α]]](Leibniz.refl)
}

object BoundedLeibniz {
  private[this] final case class Refl[A]() extends BL[A, A, A, A] {
    def subst[F[_ >: A <: A]](fa: F[A]): F[A] = fa
  }
  private[this] val anyRefl: BL[Nothing, Any, Any, Any] = Refl[Any]()

  /**
    * Unsafe coercion between types. `unsafeForce` abuses `asInstanceOf` to
    * explicitly coerce types. It is unsafe, but needed where Leibnizian
    * equality isn't sufficient.
    */
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def unsafeForce[L, H >: L, A >: L <: H, B >: L <: H]: BoundedLeibniz[L, H, A, B] =
    anyRefl.asInstanceOf[BoundedLeibniz[L, H, A, B]]

  final def bound[L, H >: L, A >: L <: H, B >: L <: H]
  (ab: Leibniz[A, B]): BoundedLeibniz[L, H, A, B] =
    unsafeForce[L, H, A, B]

  /**
    * Equality is reflexive relation.
    */
  def refl[A]: BL[A, A, A, A] =
    unsafeForce[A, A, A, A]

  /**
    * Equality is reflexive relation. Compared to [[refl]], this function
    * can be used to specify bounds up front instead of relying on subtyping.
    */
  def refl_[L, H >: L, A >: L <: H]: BL[L, H, A, A] =
    unsafeForce[L, H, A, A]

  /**
    * Substitution on identity brings about a direct coercion function of the
    * same form that `=:=` provides.
    *
    * @see [[BoundedLeibniz.apply]]
    */
  def coerce[L, H >: L, A >: L <: H, B >: L <: H]
  (a: A, ab: BL[L, H, A, B]): B =
    ab.subst[λ[α => α]](a)

  /**
    * Equality is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[BoundedLeibniz.compose]]
    * @see [[BoundedLeibniz.andThen]]
    */
  def trans[L, H >: L, A >: L <: H, B >: L <: H, C >: L <: H]
  (bc: BL[L, H, B, C], ab: BL[L, H, A, B]): BL[L, H, A, C] =
    bc.subst[λ[`α >: L <: H` => BL[L, H, A, α]]](ab)

  /**
    * Equality is symmetric and therefore can be flipped around.
    *
    * @see [[Leibniz.flip]]
    */
  def symm[L, H >: L, A >: L <: H, B >: L <: H]
  (ab: BL[L, H, A, B]): BL[L, H, B, A] =
    ab.subst[λ[`α >: L <: H` => BL[L, H, α, A]]](refl)

  /**
    * Given `A === B` we can prove that `F[A] === F[B]`.
    *
    * @see [[lift2]]
    * @see [[lift3]]
    */
  def lift[
    L, H >: L, A >: L <: H, B >: L <: H,
    LF, HF >: LF, F[_ >: L <: H] >: LF <: HF
  ] (
    eq: BL[L, H, A, B]
  ): BL[LF, HF, F[A], F[B]] = {
    type f[α >: L <: H] = BL[LF, HF, F[A], F[α]]
    eq.subst[f](refl_[LF, HF, F[A]])
  }

  /**
    * Given `A === B` and `I === J` we can prove that `F[A, I] === F[B, J]`.
    *
    * @see [[lift]]
    * @see [[lift3]]
    */
  def lift2[
    L1, H1 >: L1, A1 >: L1 <: H1, B1 >: L1 <: H1,
    L2, H2 >: L2, A2 >: L2 <: H2, B2 >: L2 <: H2,
    LF, HF >: LF, F[_ >: L1 <: H1, _ >: L2 <: H2] >: LF <: HF
  ] (
    eq1: BL[L1, H1, A1, B1],
    eq2: BL[L2, H2, A2, B2]
  ): BL[LF, HF, F[A1, A2], F[B1, B2]] = {
    type f1[α >: L1 <: H1] = BL[LF, HF, F[A1, A2], F[α, A2]]
    type f2[α >: L2 <: H2] = BL[LF, HF, F[A1, A2], F[B1, α]]
    eq2.subst[f2](eq1.subst[f1](refl_[LF, HF, F[A1, A2]]))
  }

  /**
    * Given `A === B`, `I === J`, and `M === N` we can prove that
    * `F[A, I] === F[B, J]`.
    *
    * @see [[lift]]
    * @see [[lift2]]
    */
  def lift3[
    L1, H1 >: L1, A1 >: L1 <: H1, B1 >: L1 <: H1,
    L2, H2 >: L2, A2 >: L2 <: H2, B2 >: L2 <: H2,
    L3, H3 >: L3, A3 >: L3 <: H3, B3 >: L3 <: H3,
    LF, HF >: LF, F[_ >: L1 <: H1, _ >: L2 <: H2, _ >: L3 <: H3] >: LF <: HF
  ] (
    eq1: BL[L1, H1, A1, B1],
    eq2: BL[L2, H2, A2, B2],
    eq3: BL[L3, H3, A3, B3]
  ): BL[LF, HF, F[A1, A2, A3], F[B1, B2, B3]] = {
    type f1[α >: L1 <: H1] = BL[LF, HF, F[A1, A2, A3], F[α, A2, A3]]
    type f2[α >: L2 <: H2] = BL[LF, HF, F[A1, A2, A3], F[B1, α, A3]]
    type f3[α >: L3 <: H3] = BL[LF, HF, F[A1, A2, A3], F[B1, B2, α]]
    eq3.subst[f3](eq2.subst[f2](eq1.subst[f1](refl_[LF, HF, F[A1, A2, A3]])))
  }

  /**
    * It can be convenient to convert a [[=:=]] value into a `Leibniz` value.
    * This is not strictly valid as while it is almost certainly true that
    * `A =:= B` implies `A === B` it is not the case that you can create
    * evidence of `A === B` except via a coercion. Use responsibly.
    */
  def unsafeFromPredef[L, H >: L, A >: L <: H, B >: L <: H]
  (eq: A =:= B): BoundedLeibniz[L, H, A, B] =
    unsafeForce[L, H, A, B]
}
