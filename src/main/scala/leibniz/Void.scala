package leibniz

object Void {
  def absurd[A](v: Void): A = v

  val isNotUnit: Void =!= Unit =
    WeakApart.tight(_.flip.coerce(()))

  val isNotUnit2: (Unit === Void) => Void = _.coerce(())
}
