package leibniz
package variance

import leibniz.inhabitance.{Inhabited, Proposition}

trait Covariant[F[_]] { F =>
  import Covariant._

  def apply[A, B](implicit ab: A <~< B): F[A] <~< F[B]

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    F(ev).substCv[G](g)

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    F(ev).substCt[G](g)

  def coerce[A, B](value: F[A])(implicit ev: A <~< B): F[B] =
    F(ev).coerce(value)

  def widen[A, B](fa: F[A])(implicit ev: A <~< B): F[B] =
    F(ev).apply(fa)

  def composeCo[G[_]](G: Covariant[G]): Covariant[λ[x => F[G[x]]]] =
    Covariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composeCt[G[_]](G: Contravariant[G]): Contravariant[λ[x => F[G[x]]]] =
    Contravariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    G.andThenCo[F](F)
}
object Covariant {
  def apply[F[_]](implicit ev: Covariant[F]): Covariant[F] = ev

  def witness[F[_]](implicit fab: F[Void] <~< F[Any]): Covariant[F] =
    witness1[F, Void, Any](StrictAs.bottomTop, fab)

  def witness1[F[_], A, B](implicit ab: A </< B, fab: F[A] <~< F[B]): Covariant[F] =
    new Covariant[F] {
      override def apply[X, Y](implicit xy: X <~< Y): F[X] <~< F[Y] =
        Is.lem[X, Y].map {
          case Right(eqv) => eqv.lift[F].toAs
          case Left(neqv) => Parametric[F].liftCv[A, B, X, Y](ab, fab, StrictAs.witness(neqv, xy))
        }.proved
    }

  implicit def reify[F[+_]]: Covariant[F] =
    witness[F](As.reify[F[Void], F[Any]])

  implicit def id: Covariant[λ[x => x]] = {
    type f[+x] = x
    reify[f]
  }

  implicit def proposition[F[_]]: Proposition[Covariant[F]] =
    (A: ¬¬[Covariant[F]]) => new Covariant[F] {
      override def apply[A, B](implicit ev: A <~< B): F[A] <~< F[B] = A.map(_[A, B]).proved
    }
}