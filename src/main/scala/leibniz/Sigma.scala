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
}