package leibniz

import leibniz.inhabitance.{Contractible, Inhabited, SingletonOf}

sealed abstract class Nat {
  def cata[F[_]](c: Nat.Cata[F]): F[this.type]
  def fold[F[_]](k: Nat.Fold[F]): F[this.type]
}
object Nat {
  final case object Z extends Nat {
    def cata[F[_]](k: Nat.Cata[F]): F[this.type] = k.z
    def fold[F[_]](k: Nat.Fold[F]): F[this.type] = k.z
  }
  type Z = Z.type

  final case class S[N](n: N)(implicit ev: N <:: Nat) extends Nat {
    def cata[F[_]](k: Nat.Cata[F]): F[this.type] = {
      val prev: F[N] = ev.pi[F](n)(new Pi[Nat, F] {
        def apply(x: Nat): F[x.type] = x.cata[F](k)
      })
      Contractible[S[N]].contract[this.type].flip
        .subst[F](k.s[N](prev))
    }
    def fold[F[_]](k: Nat.Fold[F]): F[this.type] =
      Contractible[S[N]].contract[this.type].flip
        .subst[F](k.s[N](n))
  }

  trait Cata[F[_]] {
    def z: F[Z]
    def s[N](n: F[N])(implicit ev: N <:: Nat): F[S[N]]
  }

  trait Fold[F[_]] {
    def z: F[Z]
    def s[N](n: N)(implicit ev: N <:: Nat): F[S[N]]
  }

  implicit val natEq: Eq[Nat] = (x: Nat, y: Nat) => x == y

  implicit def inhabited[N](implicit N: N <:: Nat): Inhabited[S[N]] =
    N.isInhabited.map(x => S.apply(x))

  implicit def contractible[N](implicit N: N <:: Nat): Contractible[S[N]] =
    Contractible.force[S[N]](inhabited[N])

  implicit def singleton[N](implicit N: N <:: Nat): S[N] <:: Nat =
    SingletonOf.witness(inhabited[N].contradicts, As.refl[S[N]], contractible[N].prop)
}