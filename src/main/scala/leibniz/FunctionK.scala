package leibniz

object FunctionK {
  type Base <: AnyRef
  trait Tag
  type Type[F[_], G[_]] <: Base with Tag

  implicit final class Ops[F[_], G[_]](val fg: Type[F, G]) extends AnyVal {
    def specialize[A]: F[A] => G[A] =
      fg.asInstanceOf[F[A] => G[A]]

    def apply[A](fa: F[A]): G[A] =
      specialize[A](fa)

    def toForall: Forall[λ[x => F[x] => G[x]]] =
      Forall.witness[λ[x => F[x] => G[x]]](specialize)
  }

  implicit final class $MkFunctionK(val t: FunctionK.type) extends AnyVal {
    type Hidden

    def witness[F[_], G[_]](fa: F[Hidden] => G[Hidden]): Type[F, G] =
      fa.asInstanceOf[Type[F, G]]

    def witnessT[F[_], G[_]](ft: TypeHolder[Hidden] => F[Hidden] => G[Hidden]): Type[F, G] =
      witness(ft(TypeHolder[Hidden]))
  }
}