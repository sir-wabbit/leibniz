package leibniz

trait Constant[F[_]] {
  def proof[A, B]: F[A] === F[B]
}
object Constant {
  def apply[F[_]](implicit ev: Injective[F]): Injective[F] = ev

  private[this] final class UnitIsConstant() extends Constant[λ[X => Unit]] {
    def proof[A, B]: Unit === Unit = Is.refl[Unit]
  }
  private[this] val instance: Constant[λ[X => Unit]] = new UnitIsConstant()

  /**
    * `unsafeForce` abuses `asInstanceOf` to explicitly coerce types.
    * It is unsafe, and not necessary in most cases, but might be used
    * to reduce allocations.
    */
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def unsafeForce[F[_]]: Constant[F] = instance.asInstanceOf[Constant[F]]

  implicit def const[A]: Constant[λ[X => A]] = unsafeForce[λ[X => A]]
}