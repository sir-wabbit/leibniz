package leibniz
package inhabitance

import leibniz.internal.Unsafe

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

  def contract[C](implicit C: Inhabited[C], ca: C <~< A): C === A =
    isContractible.contract[C](ca, C)
  def contract_(c: A): c.type === A =
    contract[c.type](Inhabited.value(c), As.refl[c.type])

  def equal[X <: A, Y <: A](x: X, y: Y): X === Y =
    isProposition.equal[X, Y](
      As.refl[X], As.refl[Y],
      Inhabited.value(x), Inhabited.value(y))
  def equal_(x: A, y: A): x.type === y.type =
    equal[x.type, y.type](x, y)

  def pi[F[_]](a: A)(f: Pi[B, F]): F[a.type] = {
    trait Sigma[+A] {
      val x: A
      val p: x.type === a.type
    }

    val s = new Sigma[A] {
      val x = a
      val p = Is.force[x.type, a.type](Unsafe.unsafe)
    }

    val b: Sigma[B] = conforms.substCo[Sigma](s)
    b.p.subst[F](f(b.x))
  }
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