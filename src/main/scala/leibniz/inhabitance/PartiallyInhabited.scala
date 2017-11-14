package leibniz.inhabitance

import cats.~>
import leibniz.variance.Injective
import leibniz.{=!=, WeakApart}

sealed abstract class PartiallyInhabited[F[_]] {
  import PartiallyInhabited._

  type Positive
  type Negative

  def positive: Inhabited[F[Positive]]
  def negative: Uninhabited[F[Negative]]

  def unequal: Positive =!= Negative = WeakApart.witness(p =>
    p.subst[λ[x => Inhabited[F[x]]]](positive).contradicts(negative.contradicts))

  def injective: Injective[F] =
    Injective.witness2[F, λ[x => x], Positive, Negative](positive, negative)

  def imap[G[_]](to: F ~> G, from: G ~> F): PartiallyInhabited[G] =
    witness[G, Positive, Negative](positive.map(to.apply), negative.contramap(from.apply))
}
object PartiallyInhabited {
  final class Witness[F[_], P, N](P: Inhabited[F[P]], N: Uninhabited[F[N]]) extends PartiallyInhabited[F] {
    type Positive = P
    type Negative = N
    def positive: Inhabited[F[Positive]] = P
    def negative: Uninhabited[F[Negative]] = N
  }

  def witness[F[_], P, N](P: Inhabited[F[P]], N: Uninhabited[F[N]]) =
    new Witness[F, P, N](P, N)
}
