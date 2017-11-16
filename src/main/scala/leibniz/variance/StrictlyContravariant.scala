package leibniz
package variance

sealed abstract class StrictlyContravariant[F[_]] {
  import StrictlyContravariant._

  def injective: Injective[F]
  def contravariant: Contravariant[F]

  def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    contravariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    contravariant.substCt[G, A, B](g)

  def lift[A, B](ab: A <~< B): F[B] <~< F[A] =
    contravariant.lift(ab)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[B], F[A]] =
    StrictAs.witness[F[B], F[A]](
      injective.contrapositive(ab.inequality.flip),
      contravariant.lift(ab.conformity))

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
  final class Witness[F[_]](I: Injective[F], C: Contravariant[F]) extends StrictlyContravariant[F] {
    def injective: Injective[F] = I
    def contravariant: Contravariant[F] = C
  }

  def apply[F[_]](implicit F: StrictlyContravariant[F]): StrictlyContravariant[F] = F

  implicit def witness[F[_]](implicit I: Injective[F], C: Contravariant[F]): StrictlyContravariant[F] =
    new Witness[F](I, C)
}