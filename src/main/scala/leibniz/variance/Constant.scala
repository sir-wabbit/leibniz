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
    witness[λ[x => F[G[x]]], Void, Unit](Void.isNotUnit, proof[G[Void], G[Unit]])

  def andThenCo[G[_]](implicit G: Covariant[G]): Constant[λ[x => G[F[x]]]] = {
    val p : F[Void] <~< F[Unit] = F.proof[Void, Unit].toAs
    val q : F[Unit] <~< F[Void] = F.proof[Unit, Void].toAs
    val r: G[F[Void]] === G[F[Unit]] = As.bracket(G.lift(p), G.lift(q))(Unsafe.unsafe)

    witness[λ[x => G[F[x]]], Void, Unit](Void.isNotUnit, r)
  }

  def andThenCt[G[_]](implicit G: Contravariant[G]): Constant[λ[x => G[F[x]]]] = {
    val p : F[Void] <~< F[Unit] = F.proof[Void, Unit].toAs
    val q : F[Unit] <~< F[Void] = F.proof[Unit, Void].toAs
    val r: G[F[Void]] === G[F[Unit]] = As.bracket(G.lift(q), G.lift(p))(Unsafe.unsafe)

    witness[λ[x => G[F[x]]], Void, Unit](Void.isNotUnit, r)
  }

  def asCovariant: Covariant[F] = Covariant.witness[F, Void, Unit](
    Void.isNotUnit, As.reify[Void, Unit], proof[Void, Unit].toAs)

  def asContravariant: Contravariant[F] = Contravariant.witness[F, Void, Unit](
    Void.isNotUnit, As.reify[Void, Unit], proof[Unit, Void].toAs)
}
trait ConstantLowerPriority {
  implicit def mkConstant[F[_]]: Constant[F] =
    macro internal.MacroUtil.mkConstant[F]
}
object Constant extends ConstantLowerPriority {
  private[leibniz] final class Witness[F[_], A, B](ab: A =!= B, fab: F[A] === F[B]) extends Constant[F] {
    def subst[G[_], X, Y](g: G[F[X]]): G[F[Y]] =
      Axioms.tcParametricity[F, A, B, X, Y](fab, ab.contradicts).subst[G](g)
  }

  implicit def proposition[F[_]]: Proposition[Constant[F]] = {
    import leibniz.internal.Unsafe._
    Proposition.force[Constant[F]]
  }

  def apply[F[_]](implicit ev: Constant[F]): Constant[F] = ev

  def witness[F[_], A, B](nab: A =!= B, fab: F[A] === F[B]): Constant[F] =
    new Witness[F, A, B](nab, fab)

  implicit def const[A]: Constant[λ[X => A]] =
    witness[λ[X => A], Void, Unit](Void.isNotUnit, Is.refl[A])

  def bracket[F[_]](covariant: Covariant[F], contravariant: Contravariant[F]): Constant[F] = {
    val p :   Void  <~<   Unit  = As.reify[Void, Unit]
    val q : F[Void] <~< F[Unit] = covariant.lift(p)
    val r : F[Unit] <~< F[Void] = contravariant.lift(p)
    val s : F[Void] === F[Unit] = Axioms.bracket(q, r)(Unsafe.unsafe)
    witness[F, Void, Unit](Void.isNotUnit, s)
  }

  /**
    * `unsafeForce` abuses `asInstanceOf` to explicitly coerce types.
    * It is unsafe, and not necessary in most cases, but might be used
    * to reduce allocations.
    */
  def force[F[_]](implicit unsafe: Unsafe): Constant[F] =
    unsafe.coerceK2_2[Constant, F](const)
}