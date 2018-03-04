import leibniz.inhabitance.SingletonOf

package object leibniz {
  type Void <: Nothing with Void.Tag

  type ¬[-A] = A => Void
  type ¬¬[A] = inhabitance.Inhabited[A]

  type ===[A, B]   = Is[A, B]
  type =!=[A, B]   = WeakApart[A, B]

  type <~<[-A, +B] = As[A, B]
  type </<[-A, +B] = StrictAs[A, B]

  type <~>[ A,  B] = Comparable[A, B]
  type >~<[ A,  B] = Incomparable[A, B]

  type =~=[A[_], B[_]] = IsK[A, B]

  type <::[A, +B] = SingletonOf[A, B]

  type TypeHolder[T] <: (Unit { type Type = T }) with TypeHolder.Tag

  type Implies[A, B] = Implies.Type[A, B]
  type |-[A, B] = Implies.Type[A, B]

  type Forall[F[_]] = Forall.Type[F]
  type \-/[F[_]]    = Forall.Type[F]

  type ~>[F[_], G[_]] = FunctionK.Type[F, G]
}
