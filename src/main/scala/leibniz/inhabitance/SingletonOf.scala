package leibniz
package inhabitance

/**
  * Witnesses that all `(a: A)` are equal, that [[A <~< B]],
  * and that [[A]] is inhabited.
  */
sealed abstract class SingletonOf[A, +B] { ab =>
  import SingletonOf._

  def conforms: A <~< B

  def isInhabited: Inhabited[A]

  def isProposition: Proposition[A]

  def isContractible: Contractible[A]

  def andThen[BB >: B, C](bc: SingletonOf[BB, C]): SingletonOf[A, C] =
    witness[A, C](isInhabited.contradicts, conforms andThen bc.conforms, isProposition)

  def compose[Z](za: SingletonOf[Z, A]): SingletonOf[Z, B] =
    za andThen ab
}
object SingletonOf {
  private[this] final class Witness[A, B]
  (proof: (A => Void) => Void,
   val conforms: A <~< B,
   val isProposition: Proposition[A]
  ) extends SingletonOf[A, B] {
    val isInhabited: Inhabited[A] = Inhabited.witness[A](proof)

    val isContractible: Contractible[A] = Contractible.witness[A](isInhabited, isProposition)
  }

  def apply[A, B](implicit ev: SingletonOf[A, B]): SingletonOf[A, B] = ev

  def witness[A, B](proof: (A => Void) => Void, conformity: A <~< B,
                    proposition: Proposition[A]): SingletonOf[A, B] =
    new Witness[A, B](proof, conformity, proposition)

  implicit def refl[A <: Singleton](implicit A: ValueOf[A]): SingletonOf[A, A] =
    witness[A, A](f => f(A.value), As.refl[A], Proposition.singleton[A])
}