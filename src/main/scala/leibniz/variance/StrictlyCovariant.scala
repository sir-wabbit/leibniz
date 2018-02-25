package leibniz
package variance

import leibniz.inhabitance.{Inhabited, Proposition}

trait StrictlyCovariant[F[_]] { F =>
  import StrictlyCovariant._

  def apply[A, B](implicit ab: A </< B): F[A] </< F[B]

  val injective: Injective[F] = new Injective[F] {
    override def apply[X, Y](implicit ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj(F[Void, Any](StrictAs.bottomTop).inequality[F[Void], F[Any]], ev)
  }

  val covariant: Covariant[F] = new Covariant[F] {
    override def apply[A, B](implicit ab: A <~< B): F[A] <~< F[B] =
      Inhabited.lem[A === B].map {
        case Right(ab) => ab.lift[F].toAs
        case Left(nab) => F(StrictAs.witness(WeakApart(nab), ab)).conformity
      }.proved
  }

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    covariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    covariant.substCt[G, A, B](g)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[A], F[B]] =
    StrictAs.witness[F[A], F[B]](
      injective.contrapositive(ab.inequality),
      covariant(ab.conformity))

  def composeCo[G[_]](G: StrictlyCovariant[G]): StrictlyCovariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](
      injective.compose[G](G.injective),
      covariant.composeCo[G](G.covariant))

  def composeCt[G[_]](G: StrictlyContravariant[G]): StrictlyContravariant[λ[x => F[G[x]]]] =
    StrictlyContravariant.witness[λ[x => F[G[x]]]](
      injective.compose[G](G.injective),
      covariant.composeCt[G](G.contravariant))

  def composeCoNS[G[_]](G: Covariant[G]): Covariant[λ[x => F[G[x]]]] =
    covariant.composeCo[G](G)

  def composeCtNS[G[_]](G: Contravariant[G]): Contravariant[λ[x => F[G[x]]]] =
    covariant.composeCt[G](G)

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    covariant.composePh[G](G)
}
object StrictlyCovariant {
  def apply[F[_]](implicit F: StrictlyCovariant[F]): StrictlyCovariant[F] = F

  implicit def witness[F[_]](implicit I: Injective[F], C: Covariant[F]): StrictlyCovariant[F] = new StrictlyCovariant[F] {
    override def apply[A, B](implicit ab: A </< B): F[A] </< F[B] =
      StrictAs.witness[F[A], F[B]](
        WeakApart(fab => ab.inequality(I(fab))),
        C[A, B](ab.conformity))
  }

  implicit def proposition[F[_]]: Proposition[StrictlyCovariant[F]] =
    (A: ¬¬[StrictlyCovariant[F]]) => new StrictlyCovariant[F] {
      override def apply[A, B](implicit ab: A </< B): F[A] </< F[B] = A.map(_[A, B]).proved
    }
}