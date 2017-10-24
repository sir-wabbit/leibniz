package leibniz

import leibniz.inhabitance.Proposition

final case class Cont[R, +A](run: (A => R) => R) {
  def map[B](f: A => B): Cont[R, B] =
    Cont(k => run(a => k(f(a))))

  def flatMap[B](f: A => Cont[R, B]): Cont[R, B] =
    Cont[R, B](nb => run(a => f(a).run(b => nb(b))))

  def complete(implicit p: A <~< R): R = {
    type f[+x] = Cont[R, x]
    p.substCo[f](this).run(identity[R])
  }
}
object Cont {
  def pure[R, A](a: A): Cont[R, A] = Cont[R, A](k => k(a))

  def either[R, A]: Cont[R, Either[A => R, A]] =
    Cont(k => k(Left(a => k(Right(a)))))

  def and[R, A, B](f: (A, B) => R): Cont[R, Either[A => R, B => R]] =
    Cont(p => p(Right(b => p(Left(a => f(a, b))))))

  def imp[R, A, B](f: A => B): Cont[R, Either[A => R, B]] =
    Cont(k => k(Left(a => k(Right(f(a))))))

  def pierce[R, A]: Cont[R, ((A => R) => A) => A] =
    Cont(k => k((p: (A => R) => A) => p((a: A) => k(_ => a))))

  def lift[R, A](f: (A => R) => R): Cont[R, A] =
    Cont(f)
}