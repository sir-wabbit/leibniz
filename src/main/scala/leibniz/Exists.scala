package leibniz

import cats.~>

trait Exists[F[_]] { fa =>
  type A
  def apply: F[A]

  def mapK[G[_]](fg: F ~> G): ∃[G] =
    new ∃[G] {
      type A = fa.A
      def apply: G[fa.A] = fg.apply(fa.apply)
    }

  def fold[Z](f: F ~> λ[α => Z]): Z =
    f.apply(fa.apply)

  def toScala: F[A] forSome { type A } = apply
}
object Exists {
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def fromScala[F[_]](fa: F[X] forSome { type X }): ∃[F] =
    new ∃[F] {
      type A = Any
      def apply: F[Any] = fa.asInstanceOf[F[Any]]
    }
}
