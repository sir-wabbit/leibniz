package leibniz
package variance

import leibniz.inhabitance.Proposition

trait Constant[F[_]] { F =>
  import Constant._

  def apply[A, B]: F[A] === F[B]

  /**
    * Constant type constructors are not injective.
    */
  def notInjective(injF: Injective[F]): Void =
    injF(F[Unit, Void]).coerce(())

  def subst[G[_], A, B](g: G[F[A]]): G[F[B]] =
    F[A, B].subst[G](g)

  def compose[G[_]]: Constant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F[G[Void], G[Any]])

  def andThenCo[G[_]](implicit G: Covariant[G]): Constant[λ[x => G[F[x]]]] =
    witness[λ[x => G[F[x]]]](As.bracket(G(F[Void, Any].toAs), G(F[Any, Void].toAs)))

  def andThenCt[G[_]](implicit G: Contravariant[G]): Constant[λ[x => G[F[x]]]] =
    witness[λ[x => G[F[x]]]](As.bracket(G(F[Any, Void].toAs), G(F[Void, Any].toAs)))

  def asCovariant: Covariant[F] =
    Covariant.witness[F](F[Void, Any].toAs)

  def asContravariant: Contravariant[F] =
    Contravariant.witness[F](F[Any, Void].toAs)
}

trait ConstantLowerPriority {
  implicit def mkConstant[F[_]]: Constant[F] =
    macro internal.MacroUtil.mkConstant[F]
}

object Constant extends ConstantLowerPriority {
  def apply[F[_]](implicit ev: Constant[F]): Constant[F] = ev

  def witness[F[_]](fab: F[Void] === F[Any]): Constant[F] =
    witness1[F, Void, Any](Void.isNotAny, fab)

  def witness1[F[_], A, B](nab: A =!= B, fab: F[A] === F[B]): Constant[F] = new Constant[F] {
    def apply[X, Y]: F[X] === F[Y] = Parametric[F].liftPh[A, B, X, Y](nab, fab)
  }

  implicit def const[A]: Constant[λ[X => A]] =
    witness[λ[X => A]](Is.refl[A])

  def bracket[F[_]](cvF: Covariant[F], ctF: Contravariant[F]): Constant[F] = {
    val p :   Void  <~<   Any  = As.bottomTop
    val s : F[Void] === F[Any] = Axioms.bracket(cvF(p), ctF(p))
    witness[F](s)
  }

  implicit def proposition[F[_]]: Proposition[Constant[F]] =
    (A: ¬¬[Constant[F]]) => new Constant[F] {
      override def apply[A, B]: F[A] === F[B] = A.map(_[A, B]).proved
    }
}