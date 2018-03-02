package leibniz.inhabitance

//import cats.~>
import leibniz.variance.{Constant, Injective}
import leibniz.{=!=, WeakApart}

sealed abstract class PartiallyInhabited[F[_]] {
  import PartiallyInhabited._

  /**
    * A positive type argument. `F[Positive]` is inhabited.
    */
  type Positive

  /**
    * A negative type argument. `F[Negative]` is uninhabited.
    */
  type Negative

  /**
    * A proof that `F[Positive]` is inhabited.
    */
  def positive: Inhabited[F[Positive]]

  /**
    * A proof that `F[Negative]` is uninhabited.
    */
  def negative: Uninhabited[F[Negative]]

  /**
    * Since `F[Positive]` is inhabited, and `F[Negative]` is uninhabited,
    * an equality between [[Positive]] and [[Negative]] would lead to
    * a contradiction.
    */
  def unequal: Positive =!= Negative = WeakApart.witness(p =>
    p.subst[λ[x => Inhabited[F[x]]]](positive).notUninhabited(negative))

  /**
    * Partially inhabited type constructors are necessarily injective.
    */
  def injective: Injective[F] =
    Injective.witness3[F, λ[x => x], Positive, Negative](positive, negative)

  /**
    * Given two total natural transformations `F ~> G` and `G ~> F`,
    * we can transform a positive (inhabited) value `F[Positive]` into
    * `G[Positive]` and negative `F[Negative]` into `G[Negative]`.
    * This implies that [[G]] is partially inhabited as well.
    */
//  def imap[G[_]](to: F ~> G, from: G ~> F): PartiallyInhabited[G] =
//    witness[G, Positive, Negative](positive.map(to.apply), negative.contramap(from.apply))

  def notTotallyInhabited(t: TotallyInhabited[F]): Void =
    negative.notInhabited(t.proof[Negative])

  def notTotallyUninhabited(t: TotallyUninhabited[F]): Void =
    positive.notUninhabited(t.proof[Positive])

  def notConstant(F: Constant[F]): Void =
    F[Positive, Negative].subst(positive).notUninhabited(negative)
}
object PartiallyInhabited {
  final class Witness[F[_], P, N](P: Inhabited[F[P]], N: Uninhabited[F[N]]) extends PartiallyInhabited[F] {
    type Positive = P
    type Negative = N
    def positive: Inhabited[F[Positive]] = P
    def negative: Uninhabited[F[Negative]] = N
  }

  /**
    * Witness that [[F]] is a partially inhabited type constructor by providing
    * evidence that `F[P]` is inhabited and `F[N]` is uninhabited.
    */
  def witness[F[_], P, N](P: Inhabited[F[P]], N: Uninhabited[F[N]]) =
    new Witness[F, P, N](P, N)
}
