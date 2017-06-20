package leibniz

trait VoidImpl {
  type T <: Nothing

  def isNothing: T === Nothing
}
