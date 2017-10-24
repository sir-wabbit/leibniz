package leibniz.variance

import leibniz._
import leibniz.inhabitance.Proposition

sealed trait Contravariant[F[_]] { F =>
  import Contravariant._

  def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]]

  def substCt[G[-_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] = {
    type f[+x] = G[x] => G[F[B]]
    substCo[f, A, B](identity[G[F[B]]]).apply(g)
  }

  def lift[A, B](ab: A <~< B): F[B] <~< F[A] = {
    type f[+x] = F[B] <~< x
    substCo[f, A, B](As.refl[F[B]])(ab)
  }

  def widen[A, B](fa: F[B])(implicit ev: A <~< B): F[A] =
    lift(ev).apply(fa)

  def composeCo[G[_]](G: Covariant[G]): Contravariant[λ[x => F[G[x]]]] =
    new ComposeCo[F, G](F, G)

  def composeCt[G[_]](G: Contravariant[G]): Covariant[λ[x => F[G[x]]]] =
    new Covariant.CtCt[F, G](F, G)

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    G.andThenCt[F](F)
}
object Contravariant {
  implicit def proposition[F[_]]: Proposition[Contravariant[F]] = {
    import leibniz.Unsafe._
    Proposition.force[Contravariant[F]]
  }

  def apply[F[_]](implicit ev: Contravariant[F]): Contravariant[F] = ev

  private[leibniz] final case class Reified[F[-_]]() extends Contravariant[F] {
    def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] = {
      type f[-x] = G[F[x]]
      ev.substCt[f](g)
    }
  }

  private[leibniz] final case class ComposeCo[F[_], G[_]](F: Contravariant[F], G: Covariant[G]) extends Contravariant[λ[x => F[G[x]]]] {
    override def substCo[H[+_], A, B](g: H[F[G[B]]])(implicit ev: A <~< B): H[F[G[A]]] =
      F.lift(G.lift(ev)).substCo[H](g)
  }

  private[leibniz] final case class AndThenCo[F[_], G[_]](F: Covariant[F], G: Contravariant[G]) extends Contravariant[λ[x => F[G[x]]]] {
    override def substCo[H[+_], A, B](g: H[F[G[B]]])(implicit ev: A <~< B): H[F[G[A]]] =
      F.lift(G.lift(ev)).substCo[H](g)
  }

  private[leibniz] final case class WrapPh[F[_]](F: Constant[F]) extends Contravariant[F] {
    override def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: <~<[A, B]): G[F[A]] =
      F.subst[G, B, A](g)
  }

  implicit def reify[F[-_]]: Contravariant[F] = Reified[F]()

  def force[F[_]](implicit unsafe: Unsafe): Contravariant[F] = {
    type f[-x] = Any
    unsafe.coerceK2_2[Contravariant, F](reify[f])
  }
}