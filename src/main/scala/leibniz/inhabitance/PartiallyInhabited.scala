package leibniz.inhabitance

import cats.~>
import leibniz.variance.Injective
import leibniz.{=!=, WeakApart}

trait PartiallyInhabited[F[_]] {
  type Positive
  type Negative

  def positive: Inhabited[F[Positive]]
  def negative: Uninhabited[F[Negative]]

  def unequal: Positive =!= Negative = WeakApart.witness(p =>
    p.subst[λ[x => Inhabited[F[x]]]](positive).contradicts(negative.contradicts))

  def injective: Injective[F]

  def imap[G[_]](to: F ~> G, from: G ~> F): PartiallyInhabited[G]
}
