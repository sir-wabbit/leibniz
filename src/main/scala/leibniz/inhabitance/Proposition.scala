package leibniz
package inhabitance

/**
  * Witnesses that all values (a: A) are equal.
  *
  * @see [[https://ncatlab.org/nlab/show/mere+proposition]]
  */
trait Proposition[A] extends WeakProposition[A] { A =>
  def proved(implicit A: ¬¬[A]): A

  def isomap[B](f: Iso[A, B]): Proposition[B] =
    (p: ¬¬[B]) => f.to(A.proved(p.map(f.from)))

  def zip[B](implicit B: Proposition[B]): Proposition[(A, B)] =
    (proof: ¬¬[(A, B)]) => (A.proved(proof.map(_._1)), B.proved(proof.map(_._2)))
}

object Proposition {
  def apply[A](implicit A: Proposition[A]): Proposition[A] = A

  // This covers the initial object.
  implicit val voidIsProposition: Proposition[Void] =
    (p: ¬¬[Void]) => p.run(a => a)

  // This covers Unit & other terminal objects.
  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Proposition[A] =
    (_: Inhabited[A]) => A.value

  implicit def negation[A]: Proposition[¬[A]] = new Proposition[¬[A]] {
    override def proved(implicit A: ¬¬[¬[A]]): A => Void = (a: A) => {
      val nnna: ((A => Void) => Void) => Void = A.run
      nnna((k : A => Void) => k(a))
    }
  }

  // Proposition
  implicit def prop[A](implicit prop: Proposition[A]): Proposition[Proposition[A]] =
    (_: Inhabited[Proposition[A]]) => prop
}
