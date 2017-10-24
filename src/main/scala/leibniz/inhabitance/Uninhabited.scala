package leibniz.inhabitance

import leibniz.{<~<, ===, Void}

sealed trait Uninhabited[-A] {
  def contradicts(a: A): Void

  def narrow[B](implicit p: B <~< A): Uninhabited[B] =
    p.substCt[Uninhabited](this)
}
object Uninhabited {
  private[this] final class Single[A](f: A => Void) extends Uninhabited[A] {
    def contradicts(a: A): Void = f(a)
  }

  def witness[A](f: A => Void): Uninhabited[A] = new Single[A](f)

  implicit def inhabited[A](implicit A: Uninhabited[A]): Inhabited[Uninhabited[A]] =
    Inhabited.witness(A)

  implicit def uninhabited[A](implicit A: Inhabited[A]): Uninhabited[Uninhabited[A]] =
    Uninhabited.witness(nA => A.contradicts(a => nA.contradicts(a)))

  implicit def void: Uninhabited[Void] =
    witness(identity[Void])

  implicit def proposition[A]: Proposition[Uninhabited[A]] = {
    import leibniz.Unsafe._
    Proposition.force[Uninhabited[A]]
  }
}