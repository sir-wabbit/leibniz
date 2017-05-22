package leibniz

sealed abstract class Bounded[-L, +U >: L, A] private [Bounded] () {
  type Type >: L <: U
  def proof: A === Type
}
object Bounded {
  def apply[L, U >: L, A](implicit ev: Bounded[L, U, A]): Bounded[L, U, A] = ev

  final case class Refl[A]() extends Bounded[A, A, A] {
    type Type = A
    val proof: A === A = Is.refl
  }
  private[this] val reflAny: Refl[Any] = Refl[Any]()

  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def refl[A]: Bounded[A, A, A] =
    reflAny.asInstanceOf[Bounded[A, A, A]]

  implicit def reify[L, U >: L, A >: L <: U]: Bounded[L, U, A] = refl[A]
}