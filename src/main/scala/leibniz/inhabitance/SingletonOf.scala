package leibniz.inhabitance

import leibniz.{<~<, As}

/**
  * Witnesses that all `(a: A)` are equal, that [[A <~< B]],
  * and that [[A]] is inhabited.
  */
sealed abstract class SingletonOf[A, +B] { ab =>
  import SingletonOf._

  def conforms: A <~< B

  def isContractible: Contractible[A]

  def andThen[BB >: B, C](bc: SingletonOf[BB, C]): SingletonOf[A, C] = new SingletonOf[A, C] {
    override def conforms: A <~< C = ab.conforms andThen bc.conforms
    override def isContractible: Contractible[A] = ab.isContractible
  }

  def compose[Z](za: SingletonOf[Z, A]): SingletonOf[Z, B] =
    za andThen ab
}
object SingletonOf {
  private[this] final class Refl[A <: Singleton](value: A) extends SingletonOf[A, A] {
    val conforms: A <~< A = As.refl[A]
    val isContractible: Contractible[A] = Contractible.singleton[A](new ValueOf[A](value))
  }

  def apply[A, B](implicit ev: SingletonOf[A, B]): SingletonOf[A, B] = ev

  implicit def refl[A <: Singleton](implicit A: ValueOf[A]): SingletonOf[A, A] =
    new Refl[A](A.value)
}