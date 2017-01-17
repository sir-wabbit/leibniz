package object leibniz {
  type ∀[F[_]] = Forall[F]
  type ∃[F[_]] = Exists[F]

  type ===[A, B]       = Leibniz[A, B]
  type =~=[A[_], B[_]] = LeibnizK[A, B]

  type <~<[-A, +B] = Liskov[A, B]
  type >~>[+A, -B] = Liskov[B, A]
}
