package leibniz

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
  def choose[C](C: ConcreteType[C]): Either[A =!= C, B =!= C]

  /**
    * Inequality is symmetric relation and therefore can be flipped around.
    * Flipping is its own inverse, so `x.flip.flip == x`.
    */
  def flip: B =!= A = new (B =!= A) {
    def proof[F[_]](f: F[B] === F[A]): Constant[F] =
      nab.proof[F](f.flip)

    def choose[C](C: ConcreteType[C]): Either[B =!= C, A =!= C] =
      nab.choose[C](C).swap

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
object Apart {
  /**
    * Inequality is an irreflexive relation.
    */
  def irreflexive[A](ev: A =!= A): Void =
    ev.contradicts(Is.refl[A])

  private[leibniz] final case class Forced[A, B](A: ConcreteType[A], B: ConcreteType[B]) extends Apart[A, B] {
    def proof[F[_]](f: F[A] === F[B]): Constant[F] = new Constant[F] {
      def proof[X, Y]: F[X] === F[Y] = Is.unsafeForce[F[X], F[Y]]
    }

    def choose[C](C: ConcreteType[C]): Either[A =!= C, B =!= C] =
      A.compare(C) match {
        case Right(_) => B.compare(C) match {
          case Right(_) => ???
          case Left(p) => Right(p)
        }
        case Left(p) => Left(p)
      }

    override def toString: String = s"$A =!= $B"
  }
}