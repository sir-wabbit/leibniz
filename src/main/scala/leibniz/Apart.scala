package leibniz

import leibniz.internal.Unsafe
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
sealed abstract class Apart[A, B] { nab =>
  def weaken: WeakApart[A, B]
  def leftType: ConcreteType[A]
  def rightType: ConcreteType[B]

  /**
    * If `F[A]` equals to `F[B]` for unequal types `A` and `B`,
    * then `F` must be a constant type constructor.
    */
  def proof[F[_]](f: F[A] === F[B]): Constant[F] =
    weaken.proof[F](f)

  /**
    * Inequality is a co-transitive relation: if two elements
    * are apart, then any other element is apart from at least
    * one of them.
    */
  def compare[C](C: ConcreteType[C]): Either[Apart[A, C], Apart[B, C]] =
    ConcreteType.compare(leftType, C) match {
      case Right(_) => ConcreteType.compare(rightType, C) match {
        case Right(_) => ???
        case Left(p) => Right(p)
      }
      case Left(p) => Left(p)
    }

  /**
    * Inequality is symmetric relation and therefore can be flipped around.
    * Flipping is its own inverse, so `x.flip.flip == x`.
    */
  def flip: Apart[B, A] = new Apart[B, A] {
    def weaken: WeakApart[B, A] = nab.weaken.flip
    def leftType: ConcreteType[B] = nab.rightType
    def rightType: ConcreteType[A] = nab.leftType
    override def flip: Apart[A, B] = nab
  }

  /**
    * Having `A === B` and `A =!= B` at the same time leads to a contradiction.
    */
  def contradicts[R](ab: A === B): R = {
    type f[x] = x
    nab.proof[f](ab).proof[Unit, R].subst[f](())
  }

  override def toString: String = s"$leftType =!= $rightType"
}
object Apart {
  private[this] final class Instance[A, B]
  (val leftType: ConcreteType[A], val rightType: ConcreteType[B], val weaken: A =!= B)
    extends Apart[A, B]

  implicit def summon[A, B]: Apart[A, B] =
    macro internal.MacroUtil.apart[A, B]

  def make[A, B](weakApart: WeakApart[A, B], A: ConcreteType[A], B: ConcreteType[B]): Apart[A, B] =
    new Instance[A, B](A, B, weakApart)

  /**
    * Inequality is an irreflexive relation.
    */
  def irreflexive[A](ev: Apart[A, A]): Void =
    ev.contradicts(Is.refl[A])

  def force[A, B](A: ConcreteType[A], B: ConcreteType[B])(implicit unsafe: Unsafe): Apart[A, B] =
    ConcreteType.compare(A, B).left.get
}