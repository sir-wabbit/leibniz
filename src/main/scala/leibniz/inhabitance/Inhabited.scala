package leibniz.inhabitance

import leibniz.{<~<, ===, Eq, Is, Unsafe, Void}

/**
  * Witnesses that [[A]] is inhabited.
  */
sealed trait Inhabited[+A] {
  def contradicts(f: A => Void): Void

  def widen[B](implicit p: A <~< B): Inhabited[B] =
    p.substCo[Inhabited](this)
}
object Inhabited {
  private[this] final class Single[A](a: A) extends Inhabited[A] {
    def contradicts(f: A => Void): Void = f(a)
  }

  def witness[A](a: A): Inhabited[A] =
    new Single[A](a)

  implicit def inhabited[A](implicit A: Inhabited[A]): Inhabited[Inhabited[A]] =
    witness(A)

  implicit def uninhabited[A](implicit na: Uninhabited[A]): Uninhabited[Inhabited[A]] =
    Uninhabited.witness(A => A.contradicts(a => na.contradicts(a)))

  implicit def proposition[A]: Proposition[Inhabited[A]] = {
    import leibniz.Unsafe._
    Proposition.force[Inhabited[A]]
  }

  implicit def contractible[A](implicit A: Inhabited[A]): Contractible[Inhabited[A]] =
    Contractible.construct[Inhabited[A]](inhabited, proposition[A])
}