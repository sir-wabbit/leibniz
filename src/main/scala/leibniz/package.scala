import scala.annotation.unchecked.{uncheckedVariance => uV}

package object leibniz extends ForallSyntax with ExistsSyntax {
  object hacks {
    private[leibniz] type ~[-A] = A @uV
  }

  val Exists: ExistsInt   = new ExistsImpl
  val Forall: ForallInt   = new ForallImpl
  val Unknown: UnknownInt = new UnknownImpl

  type Unknown     = Unknown.T
  type UnknownK[A] = Unknown.K[A]
  type :?:         = Unknown
  type :??:[A]     = UnknownK[A]

  type ~>[A[_], B[_]] = FunctionK[A, B]

  type Void <: Nothing
  type :!: = Void
  type ⊥   = Void

  type AnyK[A] = Any
  type ⊤ = Any

  type Forall [F[_]]          = Forall.T1[F]
  type Forall2[F[_, _]]       = Forall.T2[F]
  type Forall3[F[_, _, _]]    = Forall.T3[F]
  type Forall4[F[_, _, _, _]] = Forall.T4[F]
  type ∀      [F[_]]          = Forall[F]
  type ∀∀     [F[_, _]]       = Forall2[F]
  type ∀∀∀    [F[_, _, _]]    = Forall3[F]
  type ∀∀∀∀   [F[_, _, _, _]] = Forall4[F]

  type Exists [F[_]]          = Exists.T1[F]
  type Exists2[F[_, _]]       = Exists.T2[F]
  type Exists3[F[_, _, _]]    = Exists.T3[F]
  type Exists4[F[_, _, _, _]] = Exists.T4[F]
  type ∃      [F[_]]          = Exists[F]
  type ∃∃     [F[_, _]]       = Exists2[F]
  type ∃∃∃    [F[_, _, _]]    = Exists3[F]
  type ∃∃∃∃   [F[_, _, _, _]] = Exists4[F]

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]
}
