import leibniz._
import leibniz.inhabitance.{Contractible, Inhabited, SingletonOf}

sealed abstract class Kind {
  def cata[F[_]](k: Kind.Cata[F]): F[this.type]
}
object Kind {
  final case object Star extends Kind {
    def cata[F[_]](k: Kind.Cata[F]): F[this.type] =
      k.star
  }
  type Star = Star.type

  final case class Arrow[A, B]
  (arg: A, result: B)(implicit A: A <:: Kind, B: B <:: Kind) extends Kind {
    def cata[F[_]](k: Kind.Cata[F]): F[this.type] = {

      val FA: F[A] = A.pi[F](arg)(new Pi[Kind, F] {
        override def apply(x: Kind) = x.cata[F](k)
      })

      val FB: F[B] = B.pi[F](result)(new Pi[Kind, F] {
        override def apply(x: Kind) = x.cata[F](k)
      })

      val p: this.type === (A -> B) =
        arrowIsContractible[A, B].contract[this.type](
          As.refl[this.type], Inhabited.value[this.type](this))

      p.flip.subst[F](k.arrow[A, B](FA, FB))
    }
  }

  type * = Star
  type ->[A, B] = Arrow[A, B]

  trait Cata[F[_]] {
    def star: F[*]
    def arrow[A, B](a: F[A], b: F[B])(implicit A: A <:: Kind, B: B <:: Kind): F[A -> B]
  }

  implicit val kindEq: Eq[Kind] = (x: Kind, y: Kind) => x == y

  implicit def starIsInhabited: Inhabited[Star] = Inhabited.value(Star)
  implicit def starIsContractible: Contractible[Star] = Contractible.singleton[Star]
  implicit def starIsSingleton: Star <:: Kind = SingletonOf[Star, Kind]

  implicit def arrowIsInhabited[A, B]
  (implicit A: A <:: Kind, B: B <:: Kind): Inhabited[A -> B] =
    Inhabited.map2[A, B, A -> B]((a, b) => Arrow(a, b))(A.isInhabited, B.isInhabited)
  implicit def arrowIsContractible[A, B]
  (implicit A: A <:: Kind, B: B <:: Kind): Contractible[A -> B] =
    Contractible.force[A -> B](arrowIsInhabited[A, B])
  implicit def arrowIsSingleton[A, B]
  (implicit A: A <:: Kind, B: B <:: Kind): (A -> B) <:: Kind =
    SingletonOf.witness(
      arrowIsInhabited[A, B].contradicts,
      As.refl[A -> B],
      arrowIsContractible[A, B].prop)
}