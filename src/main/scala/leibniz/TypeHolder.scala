package leibniz

@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
object TypeHolder {
  def apply[T]: TypeHolder[T] = null.asInstanceOf[TypeHolder[T]]
}
