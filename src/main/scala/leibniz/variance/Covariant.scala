package leibniz.variance

import leibniz.{<~<, As, Unsafe}

trait Covariant[F[_]] { F =>
  import Covariant._

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]]

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] = {
    type f[+a] = G[a] => G[F[A]]
    substCo[f, A, B](identity[G[F[A]]]).apply(g)
  }

  def lift[A, B](ab: A <~< B): F[A] <~< F[B] = {
    type f[+x] = F[A] <~< x
    substCo[f, A, B](As.refl[F[A]])(ab)
  }

  def widen[A, B](fa: F[A])(implicit ev: A <~< B): F[B] =
    lift(ev).apply(fa)

  def composeCo[G[_]](G: Covariant[G]): Covariant[λ[x => F[G[x]]]] =
    ComposeCo[F, G](F, G)

  def composeCt[G[_]](G: Contravariant[G]): Contravariant[λ[x => F[G[x]]]] =
    Contravariant.AndThenCo[F, G](F, G)

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    G.andThenCo[F](F)
}
object Covariant {
  def apply[F[_]](implicit ev: Covariant[F]): Covariant[F] = ev

  final case class Reified[F[+_]]() extends Covariant[F] {
    def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] = {
      type f[+x] = G[F[x]]
      ev.substCo[f](g)
    }
  }

  final case class ComposeCo[F[_], G[_]](F: Covariant[F], G: Covariant[G]) extends Covariant[λ[x => F[G[x]]]] {
    override def substCo[H[+_], A, B](g: H[F[G[A]]])(implicit ev: A <~< B): H[F[G[B]]] =
      F.lift(G.lift(ev)).substCo[H](g)
  }

  final case class CtCt[F[_], G[_]](F: Contravariant[F], G: Contravariant[G]) extends Covariant[λ[x => F[G[x]]]] {
    override def substCo[H[+_], A, B](g: H[F[G[A]]])(implicit ev: A <~< B): H[F[G[B]]] =
      F.lift(G.lift(ev)).substCo[H](g)
  }

  final case class WrapPh[F[_]](F: Constant[F]) extends Covariant[F] {
    override def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: <~<[A, B]): G[F[B]] =
      F.subst[G, A, B](g)
  }

  implicit def reify[F[+_]]: Covariant[F] = Reified[F]()

  def force[F[_]](implicit unsafe: Unsafe): Covariant[F] = {
    type f[+x] = x
    unsafe.coerceK2_2[Covariant, F](reify[f])
  }
}