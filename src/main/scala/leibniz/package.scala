package object leibniz {
  type Void <: Nothing

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]
  type =!=[A, B]       = Apart[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]
}
