package leibniz

import cats.~>

trait Forall[F[_]] { f =>
  def apply[A]: F[A]

  def mapK[G[_]](fg: F ~> G): ∀[G] =
    new ∀[G] {
      def apply[A]: G[A] = fg.apply(f.apply[A])
    }

  def lift[G[_]]: ∀[λ[α => F[G[α]]]] =
    new ∀[λ[α => F[G[α]]]] {
      def apply[A]: F[G[A]] = f.apply[G[A]]
    }

  def toFunctionK: λ[α => Unit] ~> F =
    new (λ[α => Unit] ~> F) {
      def apply[A](u: Unit): F[A] = f.apply
    }
}
object Forall {
  def fromFunctionK[F[_]](f: λ[α => Unit] ~> F): ∀[F] =
    new ∀[F] {
      def apply[A]: F[A] = f.apply(())
    }
}
