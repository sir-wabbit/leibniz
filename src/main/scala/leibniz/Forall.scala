package leibniz

trait ForallInt { f =>
  type T1[F[_]]
  type T2[F[_, _]]
  type T3[F[_, _, _]]
  type T4[F[_, _, _, _]]

  def make1[F[_]](fa: F[:?:]): T1[F]
  def make2[F[_, _]](fa: F[:?:, :?:]): T2[F]
  def make3[F[_, _, _]](fa: F[:?:, :?:, :?:]): T3[F]
  def make4[F[_, _, _, _]](fa: F[:?:, :?:, :?:, :?:]): T4[F]

  def run1[F[_], A](tf: T1[F]): F[A]
  def run2[F[_, _], A, B](tf: T2[F]): F[A, B]
  def run3[F[_, _, _], A, B, C](tf: T3[F]): F[A, B, C]
  def run4[F[_, _, _, _], A, B, C, D](tf: T4[F]): F[A, B, C, D]

  def mapK[F[_], G[_]](fa: T1[F])(fg: F ~> G): T1[G]

  def lift[F[_], G[_]](fa: T1[F]): T1[λ[α => F[G[α]]]]

  def toFunctionK[F[_], G[_]](tf: T1[F]): G ~> F
}

class ForallImpl extends ForallInt {
  final type T1[F[_]] = F[:?:]
  final type T2[F[_, _]] = F[:?:, :?:]
  final type T3[F[_, _, _]] = F[:?:, :?:, :?:]
  final type T4[F[_, _, _, _]] = F[:?:, :?:, :?:, :?:]

  final def make1[F[_]](fa: F[:?:]): T1[F] = fa
  final def make2[F[_, _]](fa: F[:?:, :?:]): T2[F] = fa
  final def make3[F[_, _, _]](fa: F[:?:, :?:, :?:]): T3[F] = fa
  final def make4[F[_, _, _, _]](fa: F[:?:, :?:, :?:, :?:]): T4[F] = fa

  final def run1[F[_], A](tf: T1[F]): F[A] = tf.asInstanceOf[F[A]]
  final def run2[F[_, _], A, B](tf: T2[F]): F[A, B] = tf.asInstanceOf[F[A, B]]
  final def run3[F[_, _, _], A, B, C](tf: T3[F]): F[A, B, C] = tf.asInstanceOf[F[A, B, C]]
  final def run4[F[_, _, _, _], A, B, C, D](tf: T4[F]): F[A, B, C, D] = tf.asInstanceOf[F[A, B, C, D]]

  final def mapK[F[_], G[_]](fa: T1[F])(fg: F ~> G): T1[G] = fg.apply(fa)

  final def lift[F[_], G[_]](fa: T1[F]): T1[λ[α => F[G[α]]]] = fa.asInstanceOf[F[G[:?:]]]

  final def toFunctionK[F[_], G[_]](tf: T1[F]): G ~> F = _ => run1[F, :?:](tf)
}

object ForallSyntax {
  final class Forall1Syntax[F[_]](val f: Forall[F]) extends AnyVal {
    def run[A]: F[A]                        = Forall.run1[F, A](f)
    def mapK[G[_]](fg: F ~> G): Forall[G]   = Forall.mapK[F, G](f)(fg)
    def lift[G[_]]: Forall[λ[α => F[G[α]]]] = Forall.lift[F, G](f)
    def toFunctionK[G[_]]:  G ~> F          = Forall.toFunctionK[F, G](f)
  }
  final class Forall2Syntax[F[_, _]](val f: Forall2[F]) extends AnyVal {
    def run[A, B]: F[A, B] = Forall.run2[F, A, B](f)
  }
  final class Forall3Syntax[F[_, _, _]](val f: Forall3[F]) extends AnyVal {
    def run[A, B, C]: F[A, B, C] = Forall.run3[F, A, B, C](f)
  }
  final class Forall4Syntax[F[_, _, _, _]](val f: Forall4[F]) extends AnyVal {
    def run[A, B, C, D]: F[A, B, C, D] = Forall.run4[F, A, B, C, D](f)
  }
}
trait ForallSyntax {
  import ForallSyntax._
  implicit final def toForall1Syntax[F[_]](fa: ∀[F]): Forall1Syntax[F] = new Forall1Syntax[F](fa)
  implicit final def toForall2Syntax[F[_, _]](fa: ∀∀[F]): Forall2Syntax[F] = new Forall2Syntax[F](fa)
  implicit final def toForall3Syntax[F[_, _, _]](fa: ∀∀∀[F]): Forall3Syntax[F] = new Forall3Syntax[F](fa)
  implicit final def toForall4Syntax[F[_, _, _, _]](fa: ∀∀∀∀[F]): Forall4Syntax[F] = new Forall4Syntax[F](fa)
}