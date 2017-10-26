package object leibniz {
  type Void <: Nothing with Void.Tag

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]
  type =!=[A, B]       = WeakApart[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]
}
