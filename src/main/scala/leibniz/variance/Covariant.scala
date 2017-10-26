package leibniz
package variance

import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

trait Covariant[F[_]] { F =>
  import Covariant._

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]]

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] = {
    type f[+a] = G[a] => G[F[A]]
    substCo[f, A, B](identity[G[F[A]]]).apply(g)
  }

  def coerce[A, B](value: F[A])(implicit ev: A <~< B): F[B] = {
    type f[+x] = x
    substCo[f, A, B](value)
  }

  def lift[A, B](ab: A <~< B): F[A] <~< F[B] = {
    type f[+x] = F[A] <~< x
    substCo[f, A, B](As.refl[F[A]])(ab)
  }

  def widen[A, B](fa: F[A])(implicit ev: A <~< B): F[B] =
    lift(ev).apply(fa)

  def composeCo[G[_]](G: Covariant[G]): Covariant[λ[x => F[G[x]]]] = {
    val p: Void <~< Unit = As.reify[Void, Unit]
    val q: F[G[Void]] <~< F[G[Unit]] = F.lift(G.lift(p))
    witness[λ[x => F[G[x]]], Void, Unit](Void.isNotUnit, p, q)
  }

  def composeCt[G[_]](G: Contravariant[G]): Contravariant[λ[x => F[G[x]]]] = {
    val p = As.reify[Void, Unit]
    val q: F[G[Unit]] <~< F[G[Void]] = F.lift(G.lift(p))
    Contravariant.witness[λ[x => F[G[x]]], Void, Unit](Void.isNotUnit, p, q)
  }

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    G.andThenCo[F](F)
}
object Covariant {
  final class Instance[F[_], A, B](ab: (A === B) => Void, p: A <~< B, q: F[A] <~< F[B]) extends Covariant[F] {
    def substCo[G[+_], X, Y](g: G[F[X]])(implicit ev: X <~< Y): G[F[Y]] = {
      val fxy = Axioms.cotcParametricity[F, A, B, X, Y](ab, p, q, ev)
      fxy.substCo[G](g)
    }
  }

  def witness[F[_], A, B](implicit ab: A =!= B, p: A <~< B, q: F[A] <~< F[B]): Covariant[F] =
    new Instance[F, A, B](ab.contradicts, p, q)

  implicit def proposition[F[_]]: Proposition[Covariant[F]] =
    Proposition.force[Covariant[F]](Unsafe.unsafe)

  def apply[F[_]](implicit ev: Covariant[F]): Covariant[F] = ev

  implicit def reify[F[+_]]: Covariant[F] =
    witness[F, Void, Unit](Void.isNotUnit, As.reify[Void, Unit], As.reify[F[Void], F[Unit]])

  def force[F[_]](implicit unsafe: Unsafe): Covariant[F] = {
    type f[+x] = x
    unsafe.coerceK2_2[Covariant, F](reify[f])
  }
}