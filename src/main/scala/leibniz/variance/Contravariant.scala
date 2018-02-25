package leibniz.variance

import leibniz._
import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

trait Contravariant[F[_]] { F =>
  import Contravariant._

  def apply[A, B](implicit ab: A <~< B): F[B] <~< F[A]

  def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    F(ev).substCv[G](g)

  def substCt[G[-_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    F(ev).substCt[G](g)

  def coerce[A, B](value: F[B])(implicit ev: A <~< B): F[A] =
    F(ev).coerce(value)

  def widen[A, B](fa: F[B])(implicit ev: A <~< B): F[A] =
    F(ev).apply(fa)

  def composeCo[G[_]](G: Covariant[G]): Contravariant[λ[x => F[G[x]]]] =
    Contravariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composeCt[G[_]](G: Contravariant[G]): Covariant[λ[x => F[G[x]]]] =
    Covariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    G.andThenCt[F](F)
}
object Contravariant {
  def apply[F[_]](implicit ev: Contravariant[F]): Contravariant[F] = ev

  def witness[F[_]](fba: F[Any] <~< F[Void]): Contravariant[F] =
    witness1[F, Void, Any](StrictAs.bottomTop, fba)

  def witness1[F[_], A, B](implicit ab: A </< B, fba: F[B] <~< F[A]): Contravariant[F] =
    new Contravariant[F] {
      override def apply[X, Y](implicit xy: X <~< Y): F[Y] <~< F[X] =
        Is.lem[X, Y].map {
          case Right(eqv) => eqv.lift[F].flip.toAs
          case Left(neqv) => Parametric[F].liftCt[A, B, X, Y](ab, fba, StrictAs.witness(neqv, xy))
        }.proved
    }

  def witness1[F[_]](implicit ev: F[Any] <~< F[Void]): Contravariant[F] =
    witness[F](ev)

  implicit def reify[F[-_]]: Contravariant[F] =
    witness[F](As.reify[F[Any], F[Void]])

  implicit def proposition[F[_]]: Proposition[Contravariant[F]] =
    (A: ¬¬[Contravariant[F]]) => new Contravariant[F] {
      override def apply[A, B](implicit ev: A <~< B): F[B] <~< F[A] = A.map(_[A, B]).proved
    }
}