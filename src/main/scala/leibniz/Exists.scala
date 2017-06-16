package leibniz


trait ExistsImpl {
  type T[F[_]] <: Any { type Type }

  def apply[F[_], A](fa: F[A]): T[F]
  def unwrap[F[_]](fa: T[F]): F[fa.Type]

  def mapK[F[_], G[_]](tf: T[F])(fg: F ~> G): T[G]

  def toScala[F[_]](tf: T[F]): F[A] forSome { type A }
  def fromScala[F[_]](fa: F[A] forSome { type A }): T[F]

  def fromInstance[F[_]](instance: Instance[F]): T[λ[X => (X, F[X])]]
}