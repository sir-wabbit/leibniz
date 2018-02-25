package leibniz
package inhabitance

import cats.Functor
import leibniz.macros.newtype

/**
  * Witnesses that [[A]] is inhabited.
  */
@newtype final case class Inhabited[A](run: (A => Void) => Void) { A =>
  import Inhabited._

  def contradicts(f: A => Void): Void = run(f)
//
//  /**
//    * If [[A]] is inhabited, then any supertype [[B]] of `A`
//    * is also inhabited.
//    */
//  def widen[B](implicit p: A <~< B): ¬¬[B] =
//    p.substCoF[Inhabited](this)

  def notUninhabited(f: Uninhabited[A]): Void =
    contradicts(f.contradicts)

  /**
    * If [[A]] is inhabited, and there is a total function
    * from [[A]] to [[B]], then `B` is also inhabited.
    */
  def map[B](f: A => B): ¬¬[B] =
    witness[B](k => A.contradicts(a => k(f(a))))

  /**
    * If [[A]] is inhabited, and you can prove that [[B]] is
    * inhabited given a value of `A`, then `B` is also inhabited.
    */
  def flatMap[B](f: A => ¬¬[B]) =
    witness[B](k => A.contradicts(a => f(a).contradicts(k)))

  /**
    * If [[A]] and [[B]] are inhabited, then a tuple `(A, B)` is
    * also inhabited.
    */
  def zip[B](b: ¬¬[B]): ¬¬[(A, B)] =
    flatMap(a => b.flatMap(b => Inhabited.value((a, b))))

  def proved(implicit ev: Proposition[A]): A =
    ev.proved(A)
}
trait InhabitedLowerPriority {
  implicit def mkInhabited[A]: ¬¬[A] =
    macro internal.MacroUtil.mkInhabited[A]
}
object Inhabited extends InhabitedLowerPriority {
  def apply[A](implicit A: ¬¬[A]): ¬¬[A] = A

//  implicit val covariant: cats.Functor[Inhabited] = new Functor[Inhabited] {
//    override def map[A, B](fa: Inhabited[A])(f: A => B): Inhabited[B] = fa.map(f)
//  }

  def witness[A](a: (A => Void) => Void): ¬¬[A] =
    Inhabited(a)

  def value[A](a: A): ¬¬[A] =
    witness[A](f => f(a))

  def map2[A, B, C](f: (A, B) => C)(implicit A: ¬¬[A], B: ¬¬[B]): ¬¬[C] =
    for { a <- A; b <- B } yield f(a, b)

  implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): ¬¬[A] =
    witness(f => f(A.value))

  implicit def inhabited[A](implicit A: ¬¬[A]): ¬¬[¬¬[A]] =
    witness(f => f(A))

  implicit def uninhabited[A](implicit na: Uninhabited[A]): Uninhabited[¬¬[A]] =
    Uninhabited.witness(A => A.notUninhabited(na))

  implicit def proposition[A]: Proposition[¬¬[A]] =
    (p: ¬¬[¬¬[A]]) => p.flatMap(identity)

  implicit def contractible[A](implicit A: ¬¬[A]): Contractible[Inhabited[A]] =
    Contractible.witness[¬¬[A]](inhabited, proposition[A])

  /**
    * Law of excluded middle.
    */
  def lem[A]: ¬¬[Either[A => Void, A]] =
    witness(k => k(Left(a => k(Right(a)))))

  def and[A, B](f: (A, B) => Void): ¬¬[Either[A => Void, B => Void]] =
    witness(p => p(Right(b => p(Left(a => f(a, b))))))

  def imp[A, B](f: A => B): ¬¬[Either[A => Void, B]] =
    witness(k => k(Left(a => k(Right(f(a))))))

  def pierce[A]: ¬¬[((A => Void) => A) => A] =
    witness(k => k((p: (A => Void) => A) => p((a: A) => k(_ => a))))
}