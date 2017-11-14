package leibniz

import org.scalatest.{FunSuite, Matchers}

import Nat.{Z, S}

class VectTest extends FunSuite with Matchers {
  sealed abstract class Vect[N, +A](implicit ev: N <:: Nat) {
    import Vect._

    def ::[B >: A](el: B): Vect[S[N], B] =
      new ::[N, B](el, this)
  }
  object Vect {
    final case object Nil extends Vect[Z, Nothing]
    final case class ::[N, A](head: A, tail: Vect[N, A])(implicit ev: N <:: Nat)
      extends Vect[S[N], A]
  }
  import Vect._

  def replicate[A](n: Nat, a: A): Vect[n.type, A] =
    n.cata[Vect[?, A]](new Nat.Cata[Vect[?, A]] {
      override def z: Vect[Z, A] = Vect.Nil
      override def s[M](n: Vect[M, A])(implicit p: M <:: Nat): Vect[S[M], A] = a :: n
    })

  test("vect-nat") {
    val two = S(S(Z))
    val v : Vect[two.type, Int] = replicate[Int](two, 1)
    println(replicate[Int](two, 1))
  }
}