package leibniz.variance

import leibniz._
import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

sealed trait Contravariant[F[_]] { F =>
  import Contravariant._

  def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]]

  def substCt[G[-_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] = {
    type f[+x] = G[x] => G[F[B]]
    substCo[f, A, B](identity[G[F[B]]]).apply(g)
  }

  def coerce[A, B](value: F[B])(implicit ev: A <~< B): F[A] = {
    type f[+x] = x
    substCo[f, A, B](value)
  }

  def lift[A, B](ab: A <~< B): F[B] <~< F[A] = {
    type f[+x] = F[B] <~< x
    substCo[f, A, B](As.refl[F[B]])(ab)
  }

  def widen[A, B](fa: F[B])(implicit ev: A <~< B): F[A] =
    lift(ev).apply(fa)

  def composeCo[G[_]](G: Covariant[G]): Contravariant[λ[x => F[G[x]]]] = {
    val p: Void <~< Unit = As.reify[Void, Unit]
    val q: F[G[Unit]] <~< F[G[Void]] = F.lift(G.lift(p))
    witness[λ[x => F[G[x]]], Void, Unit](Void.isNotUnit, p, q)
  }

  def composeCt[G[_]](G: Contravariant[G]): Covariant[λ[x => F[G[x]]]] ={
    val p: Void <~< Unit = As.reify[Void, Unit]
    val q: F[G[Void]] <~< F[G[Unit]] = F.lift(G.lift(p))
    Covariant.witness[λ[x => F[G[x]]], Void, Unit](Void.isNotUnit, p, q)
  }

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    G.andThenCt[F](F)
}
object Contravariant {
  final class Witness[F[_], A, B](ab: (A === B) => Void, p: A <~< B, q: F[B] <~< F[A]) extends Contravariant[F] {
    def substCo[G[+_], X, Y](g: G[F[Y]])(implicit ev: X <~< Y): G[F[X]] = {
      type f1[-x] = x => G[F[X]]
      type f[x] = G[F[x]] => G[F[X]]

      val q1: (G[F[A]] => G[F[X]]) <~< (G[F[B]] => G[F[X]]) = q.liftCo[G].liftCt[f1]

      val fyx: f[X] <~< f[Y] = Axioms.cotcParametricity[f, A, B, X, Y](ab, p, q1, ev)

      val fq: G[F[Y]] => G[F[X]] = fyx.coerce(identity[G[F[X]]])

      fq(g)
    }
  }

  def witness[F[_], A, B](implicit ab: A =!= B, p: A <~< B, q: F[B] <~< F[A]): Contravariant[F] =
    new Witness[F, A, B](ab.contradicts, p, q)

  implicit def proposition[F[_]]: Proposition[Contravariant[F]] =
    Proposition.force[Contravariant[F]](Unsafe.unsafe)

  def apply[F[_]](implicit ev: Contravariant[F]): Contravariant[F] = ev

  implicit def reify[F[-_]]: Contravariant[F] =
    witness[F, Void, Unit](Void.isNotUnit, As.reify[Void, Unit], As.reify[F[Unit], F[Void]])

  def force[F[_]](implicit unsafe: Unsafe): Contravariant[F] = {
    type f[-x] = Any
    unsafe.coerceK2_2[Contravariant, F](reify[f])
  }
}