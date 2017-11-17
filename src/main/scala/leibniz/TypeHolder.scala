package leibniz

object TypeHolder {
  trait Tag extends Any

  def apply[T]: TypeHolder[T] = {
    object R { val r: TypeHolder[T] = identity(r) }
    R.r
  }
}
