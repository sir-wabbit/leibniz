package leibniz

import cats.~>

trait ForallImpl { f =>
  type T[F[_]]

  def apply[F[_]](fa: F[:?:]): T[F]

  def run[F[_], A](tf: T[F]): F[A]

  def mapK[F[_], G[_]](fa: T[F])(fg: F ~> G): T[G]

  def lift[F[_], G[_]](fa: T[F]): T[λ[α => F[G[α]]]]

  def toFunctionK[F[_], G[_]](tf: T[F]): G ~> F
}