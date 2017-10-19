package leibniz

trait Cosingleton[A] {
  type Result >: A
}
object Cosingleton {
  def apply[A]: Cosingleton[A] =
    macro internal.Whitebox.cosingleton[A]
}
