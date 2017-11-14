package leibniz

import leibniz.inhabitance.{Contractible, Inhabited, SingletonOf}

import Nat.{Z, S}

sealed abstract class Fin[N] {
  def cata[F[_, _]](c: Fin.Cata[F]): F[N, this.type]
}
object Fin {
  final case class FZ[N]()(implicit N: N <:: Nat) extends Fin[N] {
    def cata[F[_, _]](cata: Fin.Cata[F]): F[N, this.type] = {
      implicit val thisInhabited: Inhabited[this.type] = Inhabited.value(this)
      val p : this.type === FZ[N] = zIsContractible.contract[this.type]
      type f[x] = F[N, x]
      p.flip.subst[f](cata.z[N])
    }
  }

  final case class FS[N, FN](n: FN)(implicit N: N <:: Nat, FN: FN <:: Fin[N]) extends Fin[S[N]] {
    def cata[F[_, _]](cata: Fin.Cata[F]): F[S[N], this.type] = {
      implicit val thisInhabited: Inhabited[this.type] = Inhabited.value(this)
      val p : this.type === FS[N, FN] = sIsContractible.contract[this.type]
      type f[x] = F[S[N], x]
      val r : F[S[N], FS[N, FN]] = cata.s[N, FN](FN.pi(n)(new Pi[Fin[N], F[N, ?]] {
        override def apply(x: Fin[N]) = x.cata[F](cata)
      }))
      p.flip.subst[f](r)
    }
  }

  trait Cata[F[_, _]] {
    def z[N](implicit N: N <:: Nat): F[N, FZ[N]]
    def s[N, FN](n: F[N, FN])(implicit N: N <:: Nat, FN: FN <:: Fin[N]): F[Nat.S[N], FS[N, FN]]
  }

  implicit val natEq: Eq[Nat] = (x: Nat, y: Nat) => x == y

  implicit def zIsInhabited[N](implicit N: N <:: Nat): Inhabited[FZ[N]] =
    Inhabited.value(FZ[N]())

  implicit def zIsContractible[N](implicit N: N <:: Nat): Contractible[FZ[N]] =
    Contractible.force[FZ[N]](zIsInhabited[N])

  implicit def zIsSingleton[N](implicit N: N <:: Nat): FZ[N] <:: Fin[N] =
    SingletonOf.witness(zIsInhabited[N].contradicts, As.refl[FZ[N]], zIsContractible[N].prop)

  implicit def sIsInhabited[N, FN](implicit N: N <:: Nat, FN: FN <:: Fin[N]): Inhabited[FS[N, FN]] =
    FN.isInhabited.map(FS[N, FN])

  implicit def sIsContractible[N, FN](implicit N: N <:: Nat, FN: FN <:: Fin[N]): Contractible[FS[N, FN]] =
    Contractible.force[FS[N, FN]](sIsInhabited[N, FN])

  implicit def sIsSingleton[N, FN](implicit N: N <:: Nat, FN: FN <:: Fin[N]): FS[N, FN] <:: Fin[Nat.S[N]] =
    SingletonOf.witness(sIsInhabited[N, FN].contradicts, As.refl[FS[N, FN]], sIsContractible[N, FN].prop)
}