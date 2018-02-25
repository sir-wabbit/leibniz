package leibniz

import leibniz.inhabitance.{Inhabited, Proposition, Uninhabited}
import leibniz.macros.newtype
import leibniz.variance.{Constant, Injective}

/**
  * In constructive mathematics, an apartness relation is a constructive
  * form of inequality, and is often taken to be more basic than equality.
  * It is often written as # to distinguish from the negation of equality
  * (the denial inequality) ≠, which is weaker.
  *
  * An apartness relation is a symmetric irreflexive binary relation with
  * the additional condition that if two elements are apart, then any other
  * element is apart from at least one of them (this last property is often
  * called co-transitivity or comparison).
  *
  * @see [[https://en.wikipedia.org/wiki/Apartness_relation
  *        Apartness relation]]
  */
@newtype final case class WeakApart[A, B](run: (A === B) => Void) { self =>
  import WeakApart._

  /**
    * Having `A === B` and `A =!= B` at the same time leads to a contradiction.
    */
  def apply(ab: A === B): Void = run(ab)

  /**
    * If `F[A]` equals to `F[B]` for unequal types `A` and `B`,
    * then `F` must be a constant type constructor.
    */
  def constant[F[_]](f: F[A] === F[B]): Constant[F] =
    Constant.witness1[F, A, B](this, f)

  def lower[F[_]]: PartialLower[F, A, B] = new PartialLower[F, A, B](this)

  /**
    * Inequality is a co-transitive relation: if two elements
    * are apart, then any other element is apart from at least
    * one of them.
    */
  def compare[C]: Inhabited[Either[A =!= C, B =!= C]] = {
    val f: (A === C, B === C) => Void = (ac, bc) => run.apply(ac andThen bc.flip)
    Inhabited.and(f).map {
      case Left(nac) => Left(witness(nac))
      case Right(nbc) => Right(witness(nbc))
    }
  }

  /**
    * Inequality is symmetric relation and therefore can be flipped around.
    * Flipping is its own inverse, so `x.flip.flip == x`.
    */
  def flip: B =!= A = WeakApart.witness[B, A](ba => self(ba.flip))

  /**
    * Strengthen the proof by providing explicit type descriptions.
    */
  def strengthen(implicit A: TypeId[A], B: TypeId[B]): Apart[A, B] =
    Apart.witness(this, A, B)

  /**
    * Given an injective [[F]], if `A ≠ B`, then `F[A] ≠ F[B]`.
    */
  def lift[F[_]](implicit F: Injective[F]): F[A] =!= F[B] =
    witness[F[A], F[B]](p => apply(F(p)))

  /**
    * Classical proof that
    * ¬(a ~ b) ⟺ a ≸ b ⋁ b < a ⋁ a < b
    */
  def decompose: ¬¬[(B </< A) Either (A </< B) Either (A >~< B)] =
    Inhabited.lem[A <~< B].flatMap {
      case Right(lte) => Inhabited.value(Left(Right(StrictAs.witness(self, lte))))
      case Left(notLTE) =>
        Inhabited.lem[B <~< A].map {
          case Right(gte) => Left(Left(StrictAs.witness(self.flip, gte)))
          case Left(notGTE) => Right(Incomparable.witness(notLTE, notGTE))
        }
    }
}
object WeakApart {
  def apply[A, B](implicit ev: WeakApart[A, B]): WeakApart[A, B] = ev

  implicit def proposition[A, B]: Proposition[WeakApart[A, B]] =
    Proposition.negation[A === B].isomap(Iso.unsafe(x => new WeakApart(x), _.run))

  implicit def inhabited[A, B](implicit A: Inhabited[A === B]): Uninhabited[A =!= B] =
    Uninhabited.witness(nab => A.contradicts(ab => nab.apply(ab)))

  implicit def uninhabited[A, B](implicit na: Uninhabited[A === B]): Inhabited[A =!= B] =
    Inhabited.value(witness(na.contradicts))

  implicit def mkWeakApart[A, B]: A =!= B =
    macro internal.MacroUtil.mkWeakApart[A, B]

  /**
    * Inequality is an irreflexive relation.
    */
  def irreflexive[A](ev: A =!= A): Void =
    ev.apply(Is.refl[A])

  def witness[A, B](f: (A === B) => Void): WeakApart[A, B] =
    new WeakApart[A, B](f)

  private[WeakApart] final class PartialLower[F[_], A, B](val ab: WeakApart[A, B]) extends AnyVal {
    def apply[X, Y](implicit A: A === F[X], B: B === F[Y]): X =!= Y =
      WeakApart(xy => ab(A andThen xy.lift[F] andThen B.flip))
  }
}