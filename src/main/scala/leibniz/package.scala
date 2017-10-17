import scala.annotation.unchecked.{uncheckedVariance => uV}

package object leibniz {
  object hacks {
    private[leibniz] type ~[-A] = A @uV
  }

  type Void <: Nothing
  type :!: = Void
  type ⊥   = Void

  type AnyK[A] = Any
  type ⊤ = Any

  type ===[A, B]       = Is[A, B]
  type =~=[A[_], B[_]] = IsK[A, B]
  type =!=[A, B]       = Apart[A, B]

  type <~<[-A, +B] = As[A, B]
  type >~>[+A, -B] = As[B, A]
}
