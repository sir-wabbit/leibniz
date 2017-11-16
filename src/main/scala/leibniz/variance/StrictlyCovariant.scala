package leibniz
package variance

sealed abstract class StrictlyCovariant[F[_]] {
  import StrictlyCovariant._

  def injective: Injective[F]
  def covariant: Covariant[F]

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    covariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    covariant.substCt[G, A, B](g)

  def lift[A, B](ab: A <~< B): F[A] <~< F[B] =
    covariant.lift(ab)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[A], F[B]] =
    StrictAs.witness[F[A], F[B]](
      injective.contrapositive(ab.inequality),
      covariant.lift(ab.conformity))

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
  final class Witness[F[_]](I: Injective[F], C: Covariant[F]) extends StrictlyCovariant[F] {
    def injective: Injective[F] = I
    def covariant: Covariant[F] = C
  }

  def apply[F[_]](implicit F: StrictlyCovariant[F]): StrictlyCovariant[F] = F

  implicit def witness[F[_]](implicit I: Injective[F], C: Covariant[F]): StrictlyCovariant[F] =
    new Witness[F](I, C)
}