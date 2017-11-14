package leibniz.variance

sealed abstract class StrictlyCovariant[F[_]] {
  def injective: Injective[F]
  def covariant: Covariant[F]
}
object StrictlyCovariant {

}