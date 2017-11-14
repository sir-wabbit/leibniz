package leibniz.variance

sealed abstract class StrictlyContravariant[F[_]] {
  def injective: Injective[F]
  def contravariant: Contravariant[F]
}
