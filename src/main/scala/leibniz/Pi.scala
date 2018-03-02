package leibniz

//import cats.~>

trait Pi[-A, F[_]] { fa =>
  def apply(x: A): F[x.type]

//  final def mapK[G[_]](fg: F ~> G): Pi[A, G] =
//    new Pi[A, G] {
//      override def apply(a: A): G[a.type] = fg.apply(fa.apply(a))
//    }

  final def narrow[B <: A]: Pi[B, F] = this

  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  final def widenK[G[x] >: F[x]]: Pi[A, G] =
    this.asInstanceOf[Pi[A, G]]
}
object Pi {
  final def and[A, F[_], G[_]](f: Pi[A, F], g: Pi[A, G]): Pi[A, λ[x => (F[x], G[x])]] =
    new Pi[A, λ[x => (F[x], G[x])]] {
      override def apply(a: A): (F[a.type], G[a.type]) = (f.apply(a), g.apply(a))
    }

  final def flip[A, B, F[_, _]](f: Pi[A, λ[a => Pi[B, λ[b => F[a, b]]]]]): Pi[B, λ[b => Pi[A, λ[a => F[a, b]]]]] =
    new Pi[B, λ[b => Pi[A, λ[a => F[a, b]]]]] {
      override def apply(b: B): Pi[A, λ[a => F[a, b.type]]] = new Pi[A, λ[a => F[a, b.type]]] {
        override def apply(a: A): F[a.type, b.type] = f.apply(a).apply(b)
      }
    }

  final def or[A, F[_], G[_]](fg: Either[Pi[A, F], Pi[A, G]]): Pi[A, λ[x => Either[F[x], G[x]]]] =
    new Pi[A, λ[x => Either[F[x], G[x]]]] {
      override def apply(a: A): Either[F[a.type], G[a.type]] = fg match {
        case Left(af) => Left(af.apply(a))
        case Right(ag) => Right(ag.apply(a))
      }
    }

  final def const[A, B](a: A): Pi[B, λ[b => a.type]] =
    new Pi[B, λ[b => a.type]] {
      override def apply(b: B): a.type = a
    }

  final def id[T]: Pi[T, λ[x => x]] =
    new Pi[T, λ[x => x]] {
      override def apply(x: T): x.type = x
    }
}