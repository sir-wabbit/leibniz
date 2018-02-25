package leibniz
package variance

import leibniz.inhabitance.{Inhabited, Proposition}

sealed abstract class StrictlyContravariant[F[_]] { F =>
  import StrictlyContravariant._

  def apply[A, B](implicit ab: A </< B): F[B] </< F[A]

  val injective: Injective[F] = new Injective[F] {
    override def apply[X, Y](implicit ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj[Void, Any, X, Y](F[Void, Any](StrictAs.bottomTop).inequality[F[Any], F[Void]].flip, ev)
  }

  val contravariant: Contravariant[F] = new Contravariant[F] {
    override def apply[A, B](implicit ab: A <~< B): F[B] <~< F[A] =
      Inhabited.lem[A === B].map {
        case Right(ab) => ab.lift[F].flip.toAs
        case Left(nab) => F(StrictAs.witness(WeakApart(nab), ab)).conformity
      }.proved
  }

  def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    contravariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    contravariant.substCt[G, A, B](g)

  def lift[A, B](ab: A <~< B): F[B] <~< F[A] =
    contravariant(ab)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[B], F[A]] =
    StrictAs.witness[F[B], F[A]](
      injective.contrapositive(ab.inequality.flip),
      contravariant(ab.conformity))

  def composeCo[G[_]](G: StrictlyCovariant[G]): StrictlyContravariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](
      injective.compose[G](G.injective),
      contravariant.composeCo[G](G.covariant))

    def composeCt[G[_]](G: StrictlyContravariant[G]): StrictlyCovariant[λ[x => F[G[x]]]] =
      StrictlyCovariant.witness[λ[x => F[G[x]]]](
        injective.compose[G](G.injective),
        contravariant.composeCt[G](G.contravariant))

  def composeCoNS[G[_]](G: Covariant[G]): Contravariant[λ[x => F[G[x]]]] =
    contravariant.composeCo[G](G)

  def composeCtNS[G[_]](G: Contravariant[G]): Covariant[λ[x => F[G[x]]]] =
    contravariant.composeCt[G](G)

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    contravariant.composePh[G](G)
}
object StrictlyContravariant {
  def apply[F[_]](implicit F: StrictlyContravariant[F]): StrictlyContravariant[F] = F

  implicit def witness[F[_]](implicit I: Injective[F], C: Contravariant[F]): StrictlyContravariant[F] = new StrictlyContravariant[F] {
    override def apply[A, B](implicit ab: A </< B): F[B] </< F[A] =
      StrictAs.witness[F[B], F[A]](
        WeakApart(fab => ab.inequality(I(fab).flip)),
        C[A, B](ab.conformity))
  }

  implicit def proposition[F[_]]: Proposition[StrictlyContravariant[F]] =
    (A: ¬¬[StrictlyContravariant[F]]) => new StrictlyContravariant[F] {
      override def apply[A, B](implicit ab: A </< B): F[B] </< F[A] = A.map(_[A, B]).proved
    }
}