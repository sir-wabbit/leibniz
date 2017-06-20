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

  type ~>[A[_], B[_]] = FunctionK[A, B]

  type Void <: Nothing

  type AnyK[A] = Any

  type ⊥ = Void
  type ⊤ = Any

  type :?:     = Unknown
  type :??:[A] = UnknownK[A]

  type :!: = Void

  type Forall[F[_]] = Forall.T[F]
  type Exists[F[_]] = Exists.T[F]
  type ∀[F[_]] = Forall[F]
  type ∃[F[_]] = Exists[F]

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]

  object hacks {
    private[leibniz] type ~[-A] = A @uV
  }

  val Exists: ExistsImpl = new ExistsImpl {
    type L[F[_], A] = F[A] { type Type = A }
    type T[F[_]]    = L[F, _]

    def apply[F[_], A](fa: F[A]): T[F] =
      fa.asInstanceOf[T[F]]
    def unwrap[F[_]](fa: T[F]): F[fa.Type] =
      fa.asInstanceOf[F[fa.Type]]

    def mapK[F[_], G[_]](tf: T[F])(fg: F ~> G): T[G] =
      fg.apply(tf.asInstanceOf[F[:?:]]).asInstanceOf[T[G]]

    def toScala[F[_]](tf: T[F]): F[A] forSome { type A } = unwrap[F](tf)
    def fromScala[F[_]](fa: F[A] forSome { type A }): T[F] =
      fa.asInstanceOf[T[F]]

    def fromInstance[F[_]](instance: Instance[F]): T[λ[X => (X, F[X])]] =
      apply[λ[X => (X, F[X])], instance.Type]((instance.first, instance.second))
  }

  implicit final class leibnizExistsOps[F[_], A](final val fa: Exists[F] { type Type = A }) extends AnyVal {
    def value: F[fa.Type] = Exists.unwrap[F](fa)

    def mapK[G[_]](fg: F ~> G): Exists[G] = Exists.mapK[F, G](fa)(fg)

    def toScala: F[A] forSome { type A } = Exists.toScala[F](fa)
  }

  val Forall: ForallImpl = new ForallImpl {
    type T[F[_]] = F[:?:]

    def apply[F[_]](fa: F[:?:]): T[F] = fa

    def run[F[_], A](tf: T[F]): F[A] = tf.asInstanceOf[F[A]]

    def mapK[F[_], G[_]](fa: T[F])(fg: F ~> G): T[G] = fg.apply(fa)

    def lift[F[_], G[_]](fa: T[F]): T[λ[α => F[G[α]]]] = fa.asInstanceOf[F[G[:?:]]]

    def toFunctionK[F[_], G[_]](tf: T[F]): G ~> F = _ => run[F, :?:](tf)
  }

  implicit final class leibnizForallOps[F[_]](val f: Forall[F]) extends AnyVal {
    def run[A]: F[A] = Forall.run[F, A](f)

    def mapK[G[_]](fg: F ~> G): Forall[G] = Forall.mapK[F, G](f)(fg)

    def lift[G[_]]: Forall[λ[α => F[G[α]]]] = Forall.lift[F, G](f)

    def toFunctionK[G[_]]:  G ~> F = Forall.toFunctionK[F, G](f)
  }
}
