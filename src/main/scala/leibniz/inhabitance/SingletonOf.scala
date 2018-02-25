package leibniz
package inhabitance

/**
  * Witnesses that all `(a: A)` are equal, that [[A <~< B]],
  * and that [[A]] is inhabited.
  */
sealed abstract class SingletonOf[A, +B] { ab =>
  import SingletonOf._

  /**
    * A singleton type conforms to its widened type.
    */
  def conforms: A <~< B

  /**
    * A singleton type is always inhabited.
    */
  def isInhabited: Inhabited[A]

  /**
    * A singleton type is a mere proposition, all of its inhabited subtypes
    * (there is only one) are equal.
    */
  def isProposition: Proposition[A]

  /**
    * A singleton type is contractible, all of its inhabited subtypes
    * (there is only one, A) are equal to A.
    */
  def isContractible: Contractible[A]

  /**
    * If [[A]] is a singleton of type [[B]], and [[B]] is a singleton of type [[C]],
    * then [[A]] is a singleton of type [[C]]
    */
  def andThen[BB >: B, C](bc: SingletonOf[BB, C]): SingletonOf[A, C] =
    witness[A, C](isInhabited.contradicts, conforms andThen bc.conforms, isProposition)

  /**
    * If [[Z]] is a singleton of type [[A]], and [[A]] is a singleton of type [[B]],
    * then [[Z]] is a singleton of type [[B]]
    */
  def compose[Z](za: SingletonOf[Z, A]): SingletonOf[Z, B] =
    za andThen ab

  /**
    * All inhabited subtypes of a singleton are equal.
    */
  def contract[C](implicit C: Inhabited[C], ca: C <~< A): C === A =
    isContractible.contract[C](ca, C)

  /**
    * All inhabited subtypes of a singleton are equal.
    */
  def contract_(c: A): c.type === A =
    contract[c.type](Inhabited.value(c), As.refl[c.type])

  /**
    * All inhabited subtypes of a singleton are equal.
    */
  def equal[X <: A, Y <: A](x: X, y: Y): X === Y =
    isProposition.equal[X, Y](
      InhabitedSubset[X, A](As.refl[X], Inhabited.value(x)),
      InhabitedSubset[Y, A](As.refl[Y], Inhabited.value(y)))

  /**
    * All inhabited subtypes of a singleton are equal.
    */
  def equal_(x: A, y: A): x.type === y.type =
    equal[x.type, y.type](x, y)

  def piSigma[F[_]](a: A)(f: Pi[B, F]): Sigma[A, F] = {
    val s = Sigma[A, λ[x => x === a.type]](a)(Is.refl[a.type])
    type f[+x] = Sigma[x, λ[x => x === a.type]]
    val b: Sigma[B, λ[x => x === a.type]] = conforms.substCv[f](s)

    val p : b.first.type === a.type = b.second
    Sigma.apply[A, F](a)(b.second.subst[F](f(b.first)))
  }

  def pi[F[_]](a: A)(f: Pi[B, F]): F[A] = {
    val s = Sigma[A, λ[x => x === A]](a)(contract_(a))
    type f[+x] = Sigma[x, λ[x => x === A]]
    val b: Sigma[B, λ[x => x === A]] = conforms.substCv[f](s)

    b.second.subst[F](f(b.first))
  }

  def pi_[F[_]](a: A)(f: Pi[B, F]): F[a.type] = {
    val s = Sigma[A, λ[x => x === a.type]](a)(Is.refl[a.type])
    type f[+x] = Sigma[x, λ[x => x === a.type]]
    val b: Sigma[B, λ[x => x === a.type]] = conforms.substCv[f](s)

    b.second.subst[F](f(b.first))
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