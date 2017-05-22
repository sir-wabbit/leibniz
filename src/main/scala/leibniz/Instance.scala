package leibniz

import cats.~>

sealed trait Instance[F[_]] { fa =>
  import Instance._

  type Type
  def first: Type
  def second: F[Type]

  def mapK[G[_]](fg: F ~> G): Instance[G] =
    MkInstance((first, fg.apply(second)))

  def toScala: (A, F[A]) forSome { type A } =
    (first, second)

  def toExists: Exists[λ[X => (X, F[X])]] =
    Exists.fromScala[λ[X => (X, F[X])]]((first, second))

  override def toString = first.toString
}
object Instance {
  private final case class MkInstance[F[_], A](tuple: (A, F[A])) extends Instance[F] {
    type Type = A
    val first: A = tuple._1
    val second: F[A] = tuple._2
  }

  def fromScala[F[_]](fa: (X, F[X]) forSome { type X }): Instance[F] =
    MkInstance(fa)

  def fromExists[F[_]](exists: Exists[λ[X => (X, F[X])]]): Instance[F] =
    MkInstance(exists.value)

  def apply[F[_]]: PartialApply[F] = new PartialApply[F]
  final class PartialApply[F[_]] {
    def apply[A](a: A)(implicit A: F[A]): Instance[F] = MkInstance[F, A]((a, A))
  }

  implicit def capture[F[_], A](a: A)(implicit A: F[A]): Instance[F] = new Instance[F] {
    type Type = A
    def first: A = a
    def second: F[A] = A
  }

  def unapply[F[_]](box: Instance[F]): Option[(box.Type, F[box.Type])] =
    Option(box.first -> box.second)
}