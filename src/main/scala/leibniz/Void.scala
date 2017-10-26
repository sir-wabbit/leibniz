package leibniz

object Void {
  def absurd[A](v: Void): A = v

  val isNotUnit: (Unit === Void) => Void = _.coerce(())
}
