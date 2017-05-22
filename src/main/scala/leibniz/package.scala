package object leibniz {
  type ⊥ = Nothing
  type ⊤ = Any

  type ∀[F[_]] = Forall[F]
  type ∃[F[_]] = Exists[F]

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]

  // final class Pair { type _1; type _2}
  // type |:<[-L, A] = F { type _1=L; type _2=A}
  // type :<|[T <: F, +H] = Bounded[F#_1, F#_2, H]

  // type F = Nothing |:< Int :<| AnyVal
}
