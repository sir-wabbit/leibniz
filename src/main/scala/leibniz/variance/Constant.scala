package leibniz.variance

import leibniz._
import leibniz.inhabitance.Proposition
import leibniz.internal.Unsafe

sealed trait Constant[F[_]] { F =>
  import Constant._

  def subst[G[_], A, B](g: G[F[A]]): G[F[B]]

  def proof[A, B]: F[A] === F[B] = {
    type f[x] = F[A] === x
    subst[f, A, B](Is.refl[F[A]])
  }

  def compose[G[_]]: Constant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]], Unit, Void](Void.isNotUnit, proof[G[Unit], G[Void]])

  def andThenCo[G[_]](implicit G: Covariant[G]): Constant[λ[x => G[F[x]]]] = {
    import leibniz.internal.Unsafe._

    val p: G[F[Unit]] === G[F[Void]] =
      As.bracket(G.lift(F.proof[Unit, Void].toAs), G.lift(F.proof[Void, Unit].toAs))

    witness[λ[x => G[F[x]]], Unit, Void](Void.isNotUnit, p)
  }

  def andThenCt[G[_]](implicit G: Contravariant[G]): Constant[λ[x => G[F[x]]]] = {
    import leibniz.internal.Unsafe._

    val p: G[F[Unit]] === G[F[Void]] =
      As.bracket(G.lift(F.proof[Void, Unit].toAs), G.lift(F.proof[Unit, Void].toAs))

    witness[λ[x => G[F[x]]], Unit, Void](Void.isNotUnit, p)
  }

  def asCovariant: Covariant[F] = new Covariant.WrapPh[F](F)

  def asContravariant: Contravariant[F] = new Contravariant.WrapPh[F](F)
}
object Constant {
  private[leibniz] final class Instance[F[_], A, B](ab: (A === B) => Void, fab: F[A] === F[B]) extends Constant[F] {
    def subst[G[_], X, Y](g: G[F[X]]): G[F[Y]] =
      Axioms.typeConstructorParametricity[F, A, B, X, Y](ab, fab).subst[G](g)
  }

  implicit def proposition[F[_]]: Proposition[Constant[F]] = {
    import leibniz.internal.Unsafe._
    Proposition.force[Constant[F]]
  }

  def apply[F[_]](implicit ev: Constant[F]): Constant[F] = ev

  def witness[F[_], A, B](nab: (A === B) => Void, fab: F[A] === F[B]): Constant[F] =
    new Instance[F, A, B](nab, fab)

  implicit def const[A]: Constant[λ[X => A]] =
    witness[λ[X => A], Unit, Void](Void.isNotUnit, Is.refl[A])

  /**
    * `unsafeForce` abuses `asInstanceOf` to explicitly coerce types.
    * It is unsafe, and not necessary in most cases, but might be used
    * to reduce allocations.
    */
  def force[F[_]](implicit unsafe: Unsafe): Constant[F] =
    unsafe.coerceK2_2[Constant, F](const)
}