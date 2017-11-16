package leibniz

trait Sigma[+T, +F[_]] {
  val first: T
  val second: F[first.type]
}
object Sigma {
  def apply[T, F[_]](f: T)(s: F[f.type]): Sigma[T, F] = new Sigma[T, F] {
    val first: T = f
    @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
    val second: F[first.type] = s.asInstanceOf[F[first.type]]
  }

  final def flip[A, B, F[_, _]](f: Sigma[A, λ[a => Sigma[B, λ[b => F[a, b]]]]]): Sigma[B, λ[b => Sigma[A, λ[a => F[a, b]]]]] =
    Sigma[B, λ[b => Sigma[A, λ[a => F[a, b]]]]](f.second.first)(
      Sigma[A, λ[a => F[a, f.second.first.type]]](f.first)(f.second.second))

  final def or[A, F[_], G[_]](fg: Either[Sigma[A, F], Sigma[A, G]]): Sigma[A, λ[x => Either[F[x], G[x]]]] =
    fg match {
      case Left(af) => Sigma[A, λ[x => Either[F[x], G[x]]]](af.first)(Left(af.second))
      case Right(ag) => Sigma[A, λ[x => Either[F[x], G[x]]]](ag.first)(Right(ag.second))
    }

  final def const[A, B](a: A)(b: B): Sigma[B, λ[b => a.type]] =
    Sigma[B, λ[b => a.type]](b)(a)

  final def id[A](a: A): Sigma[A, λ[a => a]] =
    Sigma[A, λ[a => a]](a)(a)

  def summon[F[_]]: PartialSummon[F] = new PartialSummon[F]
  final class PartialSummon[F[_]](val b: Boolean = true) extends AnyVal {
    def apply[A](a: A)(implicit F: F[a.type]): Sigma[A, F] =
      apply(a)(F)
  }
}