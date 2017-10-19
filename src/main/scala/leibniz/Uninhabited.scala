package leibniz

trait Uninhabited[A] {
  def apply(a: A): Void
}
object Uninhabited {
  implicit def void: Uninhabited[Void] = (a: Void) => a
}