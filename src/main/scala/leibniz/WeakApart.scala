package leibniz

import leibniz.inhabitance.Proposition
import leibniz.variance.Constant

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
sealed abstract class WeakApart[A, B] { nab =>
  import WeakApart._

  /**
    * If `F[A]` equals to `F[B]` for unequal types `A` and `B`,
    * then `F` must be a constant type constructor.
    */
  def proof[F[_]](f: F[A] === F[B]): Constant[F]

  /**
    * Inequality is a co-transitive relation: if two elements
    * are apart, then any other element is apart from at least
    * one of them.
    */
  def compare[C]: Cont[Void, Either[A =!= C, B =!= C]] = {
    val f: (A === C, B === C) => Void = (ac, bc) => nab.contradicts(ac andThen bc.flip)
    Cont.and(f).map {
      case Left(nac) => Left(tight(nac))
      case Right(nbc) => Right(tight(nbc))
    }
  }


  /**
    * Inequality is symmetric relation and therefore can be flipped around.
    * Flipping is its own inverse, so `x.flip.flip == x`.
    */
  def flip: B =!= A = new (B =!= A) {
    def proof[F[_]](f: F[B] === F[A]): Constant[F] =
      nab.proof[F](f.flip)

    override def flip: A =!= B = nab
  }

  /**
    * Having `A === B` and `A =!= B` at the same time leads to a contradiction.
    */
  def contradicts[R](ab: A === B): R = {
    type f[x] = x
    nab.proof[f](ab).proof[Unit, R].subst[f](())
  }
}
object WeakApart {
  implicit def proposition[A, B]: Proposition[WeakApart[A, B]] = {
    import leibniz.Unsafe._
    Proposition.force[WeakApart[A, B]]
  }

  implicit def apply[A, B]: A =!= B =
    macro internal.MacroUtil.weakApart[A, B]

  /**
    * Inequality is an irreflexive relation.
    */
  def irreflexive[A](ev: A =!= A): Void =
    ev.contradicts(Is.refl[A])

  def tight[A, B](f: (A === B) => Void): WeakApart[A, B] = {
    import Unsafe._
    force[A, B]
  }

  private[leibniz] final class Forced[A, B](implicit unsafe: Unsafe) extends WeakApart[A, B] {
    def proof[F[_]](f: F[A] === F[B]): Constant[F] =
      Constant.force[F]
  }

  def force[A, B](implicit unsafe: Unsafe): WeakApart[A, B] =
    new Forced[A, B]()
}