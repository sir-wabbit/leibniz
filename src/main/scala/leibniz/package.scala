import cats.~>

import scala.annotation.unchecked.{uncheckedVariance => uV}

package object leibniz {
  trait UnknownTypes {
    type T
    type K[_]
  }
  val UnknownTypes: UnknownTypes = new UnknownTypes {
    type T = Any
    type K[_] = Any
  }
  type Unknown     = UnknownTypes.T
  type UnknownK[A] = UnknownTypes.K[A]

  val Void: VoidImpl = new VoidImpl {
    type T = Nothing
    def isNothing: T === Nothing = Is.refl[Nothing]
  }
  type Void = Void.T
  implicit def voidConformsToNothing: Void <~< Nothing = Void.isNothing.toAs
  implicit def nothingConformsToVoid: Nothing <~< Void = Void.isNothing.flip.toAs
  implicit def voidIsNothing: Void === Nothing = Void.isNothing

  type AnyK[A] = Any

  type ⊥ = Nothing
  type ⊤ = Any

  type :?:     = Unknown
  type :??:[A] = UnknownK[A]

  type :!: = Void

  type Forall[F[_]] = Forall.T[F]
  type ∀[F[_]] = Forall[F]
  type ∃[F[_]] = Exists[F]

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]

  object hacks {
    private[leibniz] type ~[-A] = A @uV
  }

  val Forall: ForallImpl = new ForallImpl {
    type T[F[_]] = F[:?:]

    def apply[F[_]](fa: F[:?:]): T[F] = fa

    def run[F[_], A](tf: T[F]): F[A] = tf.asInstanceOf[F[A]]

    def mapK[F[_], G[_]](fa: T[F])(fg: F ~> G): T[G] = fg.apply(fa)

    def lift[F[_], G[_]](fa: T[F]): T[λ[α => F[G[α]]]] = fa.asInstanceOf[F[G[:?:]]]

    def toFunctionK[F[_], G[_]](tf: T[F]): G ~> F = new (G ~> F) {
      def apply[A](fa: G[A]): F[A] = run[F, A](tf)
    }
  }

  implicit final class leibnizForallOps[F[_]](val f: Forall[F]) extends AnyVal {
    def run[A]: F[A] = Forall.run[F, A](f)

    def mapK[G[_]](fg: F ~> G): Forall[G] = Forall.mapK[F, G](f)(fg)

    def lift[G[_]]: Forall[λ[α => F[G[α]]]] = Forall.lift[F, G](f)

    def toFunctionK[G[_]]:  G ~> F = Forall.toFunctionK[F, G](f)
  }
}
