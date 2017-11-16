package leibniz

object TypeHolder {
  trait Tag extends Any

  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def apply[T]: TypeHolder[T] = ().asInstanceOf[TypeHolder[T]]
}
