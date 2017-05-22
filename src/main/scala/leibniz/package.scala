import scala.annotation.unchecked.{uncheckedVariance => uV}

package object leibniz {
  type ⊥ = Nothing
  type ⊤ = Any

  type ∀[F[_]] = Forall[F]
  type ∃[F[_]] = Exists[F]

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]

  object hacks {
    type ~[-A] = A @uV
  }
}
