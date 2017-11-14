package leibniz

sealed abstract class Subset[A, B] {
  def project(b: B): Option[b.type <:: A]

  def conformity: A <~< B

  def inject(a: A): B = conformity.apply(a)

  def andThen[C](bc: Subset[B, C]): Subset[B, C]
}
object Subset {

}