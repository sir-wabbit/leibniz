package leibniz

import leibniz.inhabitance.{Contractible, Inhabited, SingletonOf}

object VectTest {
  sealed abstract class Nat {
    def cata[F[_]](c: Nat.Cata[F]): F[this.type]
  }
  object Nat {
    final case object Z extends Nat {
      def cata[F[_]](c: Nat.Cata[F]): F[this.type] =
        c.z
    }

    type Z = Z.type

    final case class S[N](n: N)(implicit ev: N <:: Nat) extends Nat {
      def cata[F[_]](cata: Nat.Cata[F]): F[this.type] = {
        implicit val thisInhabited: Inhabited[this.type] =
          Inhabited.value(this)
        implicit val nInhabited: Inhabited[n.type] =
          Inhabited.singleton[n.type]
        implicit val NInhabited: Inhabited[N] =
          Inhabited.value(n)

        val p : this.type === S[N] =
          contractible[N].contract[this.type]
        val q : n.type === N =
          ev.contract[n.type]
        val r : n.type <~< Nat =
          q.toAs andThen ev.conforms

        val s : F[N] = q.subst[F](ev.pi[F](n)(new Pi[Nat, F] {
          override def apply(x: Nat): F[x.type] = x.cata[F](cata)
        }))

        p.flip.subst[F](cata.s[N](s))
      }
    }

    trait Cata[F[_]] {
      def z: F[Z]
      def s[N](n: F[N])(implicit ev: N <:: Nat): F[S[N]]
    }

    implicit val natEq: Eq[Nat] = (x: Nat, y: Nat) => x == y

    implicit def inhabited[N](implicit N: N <:: Nat): Inhabited[S[N]] =
      N.isInhabited.map(x => S.apply(x))

    implicit def contractible[N](implicit N: N <:: Nat): Contractible[S[N]] =
      Contractible.force[S[N]](inhabited[N])

    implicit def singleton[N](implicit N: N <:: Nat): S[N] <:: Nat =
      SingletonOf.witness(inhabited[N].contradicts, As.refl[S[N]], contractible[N].prop)
  }

  import Nat.{ Z, S }

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
}