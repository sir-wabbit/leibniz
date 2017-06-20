package leibniz

trait Injective[F[_]] {
  def proof[A, B](ab: F[A] === F[B]): A === B
}
object Injective {
  def apply[F[_]](implicit ev: Injective[F]): Injective[F] = ev

  private[this] final case class Id() extends Injective[λ[X => X]] {
    def proof[A, B](ab: A === B): A === B = ab
  }

  private[this] val idInjective: Injective[λ[X => X]] = Id()

  /**
    * `unsafeForce` abuses `asInstanceOf` to explicitly coerce types.
    * It is unsafe, but necessary in most cases.
    */
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def unsafeForce[F[_]]: Injective[F] = idInjective.asInstanceOf[Injective[F]]

  implicit val tuple1        : Injective[Tuple1]    = unsafeForce[Tuple1]
  implicit def tuple2_1[A]   : Injective[(A, ?)]    = unsafeForce[(A, ?)]
  implicit def tuple2_2[A]   : Injective[(?, A)]    = unsafeForce[(?, A)]
  implicit def tuple3_1[A, B]: Injective[(A, B, ?)] = unsafeForce[(A, B, ?)]
  implicit def tuple3_2[A, B]: Injective[(A, ?, B)] = unsafeForce[(A, ?, B)]
  implicit def tuple3_3[A, B]: Injective[(?, A, B)] = unsafeForce[(?, A, B)]
  implicit def func_1[A]     : Injective[A => ?]    = unsafeForce[A => ?]
  implicit def func_2[A]     : Injective[? => A]    = unsafeForce[? => A]
}