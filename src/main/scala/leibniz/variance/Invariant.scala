package leibniz
package variance

import leibniz.inhabitance.Proposition

trait Invariant[F[_]] { F =>
  import Invariant._

  def apply[A, B](implicit ev: A =!= B): F[A] >~< F[B]

  def injective: Injective[F] =
    Injective.witness[F](F(Void.isNotAny).notEqual)

  def composePh[G[_]](G: Constant[G]): Constant[λ[x => F[G[x]]]] =
    Constant.witness[λ[x => F[G[x]]]](G[Void, Any].lift[F])

  def composeInj[G[_]](G: Injective[G]): Invariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G.contrapositive(Void.isNotAny)))

  def composeStCv[G[_]](G: StrictlyCovariant[G]): Invariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G.injective.contrapositive(Void.isNotAny)))

  def composeStCt[G[_]](G: StrictlyContravariant[G]): Invariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G.injective.contrapositive(Void.isNotAny)))

  def composeInv [G[_]](G: Invariant[G]): Invariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G(Void.isNotAny).notEqual))

}
object Invariant {
  def apply[F[_]](implicit F: Invariant[F]): Invariant[F] = F

  def witness[F[_]](proof: F[Void] >~< F[Any]): Invariant[F] = new Invariant[F] {
    override def apply[A, B](implicit ev: A =!= B): F[A] >~< F[B] =
      Parametric[F].liftInv(StrictAs.bottomTop, proof, ev)
  }

  implicit def proposition[F[_]]: Proposition[Invariant[F]] =
    (A: ¬¬[Invariant[F]]) => new Invariant[F] {
      override def apply[A, B](implicit ev: A =!= B): F[A] >~< F[B] = A.map(_[A, B]).proved
    }
}