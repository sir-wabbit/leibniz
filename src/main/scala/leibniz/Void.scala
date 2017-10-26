package leibniz

import leibniz.inhabitance.Uninhabited
import leibniz.inhabitance.Uninhabited.witness

object Void {
  private[leibniz] trait Tag extends Any

  def absurd[A](v: Void): A = v

  val isNotUnit: Void =!= Unit =
    WeakApart.witness(_.flip.coerce(()))

  implicit def uninhabited: Uninhabited[Void] =
    witness(identity[Void])
}