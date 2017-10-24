package leibniz

trait Injective[F[_]] { F =>
  import Injective._

  def proof[A, B](ev: F[A] === F[B]): A === B

  def compose[G[_]](implicit G: Injective[G]): Injective[λ[x => F[G[x]]]] =
    Compose[F, G](F, G)

  def andThen[G[_]](implicit G: Injective[G]): Injective[λ[x => G[F[x]]]] =
    Compose[G, F](G, F)
}
object Injective {
  def apply[F[_]](implicit ev: Injective[F]): Injective[F] = ev

  final case class Id() extends Injective[λ[X => X]] {
    def proof[A, B](ab: A === B): A === B = ab
  }

  final case class Compose[F[_], G[_]](F: Injective[F], G: Injective[G]) extends Injective[λ[x => F[G[x]]]] {
    override def proof[A, B](ev: F[G[A]] === F[G[B]]): A === B =
      G.proof[A, B](F.proof[G[A], G[B]](ev))
  }

  val id: Injective[λ[X => X]] = Id()

  /**
    * `unsafeForce` abuses `asInstanceOf` to explicitly coerce types.
    * It is unsafe, but necessary in most cases.
    */
  def force[F[_]](implicit unsafe: Unsafe): Injective[F] = {
    unsafe.coerceK2_2[Injective, F].apply[λ[X => X]](id)
  }
}