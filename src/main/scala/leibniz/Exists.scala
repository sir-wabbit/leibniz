package leibniz

import cats.~>

sealed trait Exists[F[_]] { fa =>
  import Exists._

  type Type
  def value: F[Type]

  def mapK[G[_]](fg: F ~> G): Exists[G] =
    MkExists(fg.apply(value))

  def fold[Z](f: F ~> λ[α => Z]): Z =
    f.apply(fa.value)

  def toScala: F[A] forSome { type A } = value

  override def toString = value.toString
}
object Exists {
  private final case class MkExists[F[_], A](val value: F[A]) extends Exists[F] {
    type Type = A
  }

  def fromScala[F[_]](fa: F[X] forSome { type X }): Exists[F] =
    MkExists(fa)

  def fromInstance[F[_]](instance: Instance[F]): Exists[λ[X => (X, F[X])]] =
    instance.toExists
}
