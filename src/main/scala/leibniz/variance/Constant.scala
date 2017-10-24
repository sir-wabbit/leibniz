package leibniz.variance

import leibniz._
import leibniz.inhabitance.Proposition

sealed trait Constant[F[_]] { F =>
  import Constant._

  def subst[G[_], A, B](g: G[F[A]]): G[F[B]]

  def proof[A, B]: F[A] === F[B] = {
    type f[x] = F[A] === x
    subst[f, A, B](Is.refl[F[A]])
  }

  def compose[G[_]]: Constant[λ[x => F[G[x]]]] =
    new Compose[F, G](F)

  def andThenCo[G[_]](implicit G: Covariant[G]): Constant[λ[x => G[F[x]]]] =
    new AndThenCo(G, F)

  def andThenCt[G[_]](implicit G: Contravariant[G]): Constant[λ[x => G[F[x]]]] =
    new AndThenCt(G, F)

  def asCovariant: Covariant[F] = new Covariant.WrapPh[F](F)

  def asContravariant: Contravariant[F] = new Contravariant.WrapPh[F](F)
}
object Constant {
  implicit def proposition[F[_]]: Proposition[Constant[F]] = {
    import leibniz.Unsafe._
    Proposition.force[Constant[F]]
  }

  def apply[F[_]](implicit ev: Constant[F]): Constant[F] = ev

  private[leibniz] final class Const[X]() extends Constant[λ[a => X]] {
    def subst[G[_], A, B](g: G[X]): G[X] = g
  }

  private[leibniz] final class Compose[F[_], G[_]](F: Constant[F]) extends Constant[λ[a => F[G[a]]]] {
    override def subst[H[_], A, B](g: H[F[G[A]]]): H[F[G[B]]] = F.subst[H, G[A], G[B]](g)
  }

  private[leibniz] final class AndThenCo[F[_], G[_]](F: Covariant[F], G: Constant[G]) extends Constant[λ[x => F[G[x]]]] {
    override def subst[H[_], A, B](g: H[F[G[A]]]): H[F[G[B]]] = {
      import leibniz.Unsafe._
      As.bracket(F.lift(G.proof[A, B].toAs), F.lift(G.proof[B, A].toAs)).subst[H](g)
    }
  }

  private[leibniz] final class AndThenCt[F[_], G[_]](F: Contravariant[F], G: Constant[G]) extends Constant[λ[x => F[G[x]]]] {
    override def subst[H[_], A, B](g: H[F[G[A]]]): H[F[G[B]]] = {
      import leibniz.Unsafe._
      As.bracket(F.lift(G.proof[B, A].toAs), F.lift(G.proof[A, B].toAs)).subst[H](g)
    }
  }

  implicit def const[A]: Constant[λ[X => A]] = new Const[A]()

  /**
    * `unsafeForce` abuses `asInstanceOf` to explicitly coerce types.
    * It is unsafe, and not necessary in most cases, but might be used
    * to reduce allocations.
    */
  def force[F[_]](implicit unsafe: Unsafe): Constant[F] =
    unsafe.coerceK2_2[Constant, F](const)
}