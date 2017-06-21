package leibniz


trait ExistsInt {
  type T1[F[_]]          <: Any { type T }
  type T2[F[_, _]]       <: Any { type T1; type T2 }
  type T3[F[_, _, _]]    <: Any { type T1; type T2; type T3 }
  type T4[F[_, _, _, _]] <: Any { type T1; type T2; type T3; type T4 }

  final def apply[F[_], A](fa: F[A]): T1[F] = wrap1[F, A](fa)

  def wrap1[F[_], A](fa: F[A]): T1[F]
  def wrap2[F[_, _], A, B](fa: F[A, B]): T2[F]
  def wrap3[F[_, _, _], A, B, C](fa: F[A, B, C]): T3[F]
  def wrap4[F[_, _, _, _], A, B, C, D](fa: F[A, B, C, D]): T4[F]

  def unwrap1[F[_]](fa: T1[F]): F[fa.T]
  def unwrap2[F[_, _]](fa: T2[F]): F[fa.T1, fa.T2]
  def unwrap3[F[_, _, _]](fa: T3[F]): F[fa.T1, fa.T2, fa.T3]
  def unwrap4[F[_, _, _, _]](fa: T4[F]): F[fa.T1, fa.T2, fa.T3, fa.T4]

  def unwrapE1[F[_]](tf: T1[F]): F[T1] forSome { type T1 }
  def unwrapE2[F[_, _]](tf: T2[F]): F[T1, T2] forSome { type T1; type T2 }
  def unwrapE3[F[_, _, _]](tf: T3[F]): F[T1, T2, T3] forSome { type T1; type T2; type T3 }
  def unwrapE4[F[_, _, _, _]](tf: T4[F]): F[T1, T2, T3, T4] forSome { type T1; type T2; type T3; type T4 }

  def wrapE1[F[_]](tf: F[T1] forSome { type T1 }): T1[F]
  def wrapE2[F[_, _]](tf: F[T1, T2] forSome { type T1; type T2 }): T2[F]
  def wrapE3[F[_, _, _]](tf: F[T1, T2, T3] forSome { type T1; type T2; type T3 }): T3[F]
  def wrapE4[F[_, _, _, _]](tf: F[T1, T2, T3, T4] forSome { type T1; type T2; type T3; type T4 }): T4[F]

  def mapK[F[_], G[_]](tf: T1[F])(fg: F ~> G): T1[G]
  def mapK2[F[_, _], G[_, _]](tf: T2[F])(fg: F ~~> G): T2[G]
  def mapK3[F[_, _, _], G[_, _, _]](tf: T3[F])(fg: F ~~~> G): T3[G]
  def mapK4[F[_, _, _, _], G[_, _, _, _]](tf: T4[F])(fg: F ~~~~> G): T4[G]

  def fromInstance[F[_]](instance: Instance[F]): T1[λ[X => (X, F[X])]]
}

final class ExistsImpl extends ExistsInt {
  type L1[F[_], A]                   = F[A] { type T = A }
  type L2[F[_, _], A, B]             = F[A, B] { type T1 = A; type T2 = B }
  type L3[F[_, _, _], A, B, C]       = F[A, B, C] { type T1 = A; type T2 = B; type T3 = C }
  type L4[F[_, _, _, _], A, B, C, D] = F[A, B, C, D] { type T1 = A; type T2 = B; type T3 = C; type T4 = D }

  type T1[F[_]]          = L1[F, _]
  type T2[F[_, _]]       = L2[F, _, _]
  type T3[F[_, _, _]]    = L3[F, _, _, _]
  type T4[F[_, _, _, _]] = L4[F, _, _, _, _]

  def wrap1[F[_], A](fa: F[A]): T1[F] = fa.asInstanceOf[T1[F]]
  def wrap2[F[_, _], A, B](fa: F[A, B]): T2[F] = fa.asInstanceOf[T2[F]]
  def wrap3[F[_, _, _], A, B, C](fa: F[A, B, C]): T3[F] = fa.asInstanceOf[T3[F]]
  def wrap4[F[_, _, _, _], A, B, C, D](fa: F[A, B, C, D]): T4[F] = fa.asInstanceOf[T4[F]]

  def unwrap1[F[_]](fa: T1[F]): F[fa.T] = fa.asInstanceOf[F[fa.T]]
  def unwrap2[F[_, _]](fa: T2[F]): F[fa.T1, fa.T2] = fa.asInstanceOf[F[fa.T1, fa.T2]]
  def unwrap3[F[_, _, _]](fa: T3[F]): F[fa.T1, fa.T2, fa.T3] = fa.asInstanceOf[F[fa.T1, fa.T2, fa.T3]]
  def unwrap4[F[_, _, _, _]](fa: T4[F]): F[fa.T1, fa.T2, fa.T3, fa.T4] = fa.asInstanceOf[F[fa.T1, fa.T2, fa.T3, fa.T4]]

  def unwrapE1[F[_]](tf: T1[F]): F[T1] forSome { type T1 } = unwrap1[F](tf)
  def unwrapE2[F[_, _]](tf: T2[F]): F[T1, T2] forSome { type T1; type T2 } = unwrap2[F](tf)
  def unwrapE3[F[_, _, _]](tf: T3[F]): F[T1, T2, T3] forSome { type T1; type T2; type T3 } = unwrap3[F](tf)
  def unwrapE4[F[_, _, _, _]](tf: T4[F]): F[T1, T2, T3, T4] forSome { type T1; type T2; type T3; type T4 } = unwrap4[F](tf)

  def wrapE1[F[_]](tf: F[T1] forSome { type T1 }): T1[F] = tf.asInstanceOf[T1[F]]
  def wrapE2[F[_, _]](tf: F[T1, T2] forSome { type T1; type T2 }): T2[F] = tf.asInstanceOf[T2[F]]
  def wrapE3[F[_, _, _]](tf: F[T1, T2, T3] forSome { type T1; type T2; type T3 }): T3[F] = tf.asInstanceOf[T3[F]]
  def wrapE4[F[_, _, _, _]](tf: F[T1, T2, T3, T4] forSome { type T1; type T2; type T3; type T4 }): T4[F] = tf.asInstanceOf[T4[F]]

  def mapK[F[_], G[_]](tf: T1[F])(fg: F ~> G): T1[G] =
    fg.apply(tf.asInstanceOf[F[:?:]]).asInstanceOf[T1[G]]
  def mapK2[F[_, _], G[_, _]](tf: T2[F])(fg: F ~~> G): T2[G] =
    fg.apply(tf.asInstanceOf[F[Unk1, Unk2]]).asInstanceOf[T2[G]]
  def mapK3[F[_, _, _], G[_, _, _]](tf: T3[F])(fg: F ~~~> G): T3[G] =
    fg.apply(tf.asInstanceOf[F[Unk1, Unk2, Unk3]]).asInstanceOf[T3[G]]
  def mapK4[F[_, _, _, _], G[_, _, _, _]](tf: T4[F])(fg: F ~~~~> G): T4[G] =
    fg.apply(tf.asInstanceOf[F[Unk1, Unk2, Unk3, Unk4]]).asInstanceOf[T4[G]]

  def fromInstance[F[_]](instance: Instance[F]): T1[λ[X => (X, F[X])]] =
    apply[λ[X => (X, F[X])], instance.Type]((instance.first, instance.second))
}

object ExistsSyntax {
  implicit final class Exists1Syntax[F[_], A](val fa: Exists[F] { type T = A }) extends AnyVal {
    def value: F[A]                       = Exists.unwrap1[F](fa)
    def mapK[G[_]](fg: F ~> G): Exists[G] = Exists.mapK[F, G](fa)(fg)
    def toScala: F[A] forSome { type A }  = Exists.unwrap1[F](fa)
  }
  implicit final class Exists2Syntax[F[_, _], A, B]
  (val fa: Exists2[F] { type T1 = A; type T2 = B }) extends AnyVal {
    def value: F[fa.T1, fa.T2]                 = Exists.unwrap2[F](fa)
    def mapK[G[_, _]](fg: F ~~> G): Exists2[G] = Exists.mapK2[F, G](fa)(fg)
  }
  implicit final class Exists3Syntax[F[_, _, _], A, B, C]
  (val fa: Exists3[F] { type T1 = A; type T2 = B; type T3 = C }) extends AnyVal {
    def value: F[fa.T1, fa.T2, fa.T3]              = Exists.unwrap3[F](fa)
    def mapK[G[_, _, _]](fg: F ~~~> G): Exists3[G] = Exists.mapK3[F, G](fa)(fg)
  }
  implicit final class Exists4Syntax[F[_, _, _, _], A, B, C, D]
  (val fa: Exists4[F] { type T1 = A; type T2 = B; type T3 = C; type T4 = D }) extends AnyVal {
    def value: F[fa.T1, fa.T2, fa.T3, fa.T4]           = Exists.unwrap4[F](fa)
    def mapK[G[_, _, _, _]](fg: F ~~~~> G): Exists4[G] = Exists.mapK4[F, G](fa)(fg)
  }
}
trait ExistsSyntax {
  import ExistsSyntax._
  implicit final def toExists1Syntax[F[_], A]
  (fa: Exists[F] { type T = A }): Exists1Syntax[F, A] =
    new Exists1Syntax[F, A](fa)
  implicit final def toExists21Syntax[F[_, _], A, B]
  (fa: Exists2[F] { type T1 = A; type T2 = B }): Exists2Syntax[F, A, B] =
    new Exists2Syntax[F, A, B](fa)
  implicit final def toExists3Syntax[F[_, _, _], A, B, C]
  (fa: Exists3[F] { type T1 = A; type T2 = B; type T3 = C }): Exists3Syntax[F, A, B, C] =
    new Exists3Syntax[F, A, B, C](fa)
  implicit final def toExists4Syntax[F[_, _, _, _], A, B, C, D]
  (fa: Exists4[F] { type T1 = A; type T2 = B; type T3 = C; type T4 = D }): Exists4Syntax[F, A, B, C, D] =
    new Exists4Syntax[F, A, B, C, D](fa)
}