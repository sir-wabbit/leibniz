package leibniz

trait IsoK[A[_], B[_]] { ab =>
  def to[X](a: A[X]): B[X]
  def from[X](b: B[X]): A[X]

  def andThen[C[_]](bc: IsoK[B, C]): IsoK[A, C] = new IsoK[A, C] {
    def to[X](a: A[X]): C[X] = bc.to(ab.to(a))
    def from[X](c: C[X]): A[X] = ab.from(bc.from(c))
  }

  def compose[Z[_]](za: IsoK[Z, A]): IsoK[Z, B] = za.andThen(ab)

  def flip: IsoK[B, A] = new IsoK[B, A] {
    def to[X](b: B[X]): A[X] = ab.from(b)
    def from[X](a: A[X]): B[X] = ab.to(a)
    override val flip: IsoK[A, B] = ab
  }

  def and[I[_], J[_]](ij: IsoK[I, J]): IsoK[λ[x => (A[x], I[x])], λ[x => (B[x], J[x])]] =
    IsoK.total[λ[x => (A[x], I[x])], λ[x => (B[x], J[x])]](
      { case (a, i) => (ab.to(a), ij.to(i)) },
      { case (b, j) => (ab.from(b), ij.from(j)) })

  def or[I[_], J[_]](ij: IsoK[I, J]): IsoK[λ[x => Either[A[x], I[x]]], λ[x => Either[B[x], J[x]]]] =
    IsoK.total[λ[x => Either[A[x], I[x]]], λ[x => Either[B[x], J[x]]]]({
      case Left(a) => Left(ab.to(a))
      case Right(i) => Right(ij.to(i))
    }, {
      case Left(b) => Left(ab.from(b))
      case Right(j) => Right(ij.from(j))
    })
}
object IsoK {
  def apply[A[_], B[_]](implicit ab: IsoK[A, B]): IsoK[A, B] = ab

  def total[A[_], B[_]]: PartialTotal[A, B] = new PartialTotal[A, B]()
  final case class PartialTotal[A[_], B[_]](b: Boolean = true) extends AnyVal {
    type T

    @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
    def apply(ab: A[T] => B[T], ba: B[T] => A[T]): IsoK[A, B] = new IsoK[A, B] {
      def to[X](a: A[X]): B[X] = ab(a.asInstanceOf[A[T]]).asInstanceOf[B[X]]
      def from[X](b: B[X]): A[X] = ba(b.asInstanceOf[B[T]]).asInstanceOf[A[X]]
    }
  }

  final case class Refl[A[_]]() extends IsoK[A, A] {
    def to[X](a: A[X]): A[X] = a
    def from[X](b: A[X]): A[X] = b
  }

  implicit def id[A[_]]: IsoK[A, A] = Refl[A]()

  implicit def flip[A[_], B[_]](implicit ab: IsoK[A, B]): IsoK[B, A] = ab.flip

  object Product {
    type ⨂ [A[_], B[_]] = Nothing { type λ[X] = (A[X], B[X]) }
    type Id [A] = Unit

    final def associate[A[_], B[_], C[_]]: IsoK[(A ⨂ (B ⨂ C)#λ)#λ, ((A ⨂ B)#λ ⨂ C)#λ] =
      total[(A ⨂ (B ⨂ C)#λ)#λ, ((A ⨂ B)#λ ⨂ C)#λ](
        { case (a, (b, c)) => ((a, b), c) },
        { case ((a, b), c) => (a, (b, c)) })

    final def commute[A[_], B[_]]: IsoK[(A ⨂ B)#λ, (B ⨂ A)#λ] =
      total[(A ⨂ B)#λ, (B ⨂ A)#λ](
        { case (a, b) => (b, a) },
        { case (b, a) => (a, b) })

    final def unit[A[_]]: IsoK[A, (A ⨂ Id)#λ] =
      total[A, (A ⨂ Id)#λ](
        { case a => (a, ()) },
        { case (a, ()) => a })

    final def first[A[_], B[_], C[_]](iso: IsoK[A, C]): IsoK[(A ⨂ B)#λ, (C ⨂ B)#λ] =
      iso and id

    final def second[A[_], B[_], C[_]](iso: IsoK[B, C]): IsoK[(A ⨂ B)#λ, (A ⨂ C)#λ] =
      id and iso
  }

  object Coproduct {
    type ⨂ [A[_], B[_]] = Nothing { type λ[X] = Either[A[X], B[X]] }
    type Id [A] = Void

    final def associate[A[_], B[_], C[_]]: IsoK[(A ⨂ (B ⨂ C)#λ)#λ, ((A ⨂ B)#λ ⨂ C)#λ] =
      total[(A ⨂ (B ⨂ C)#λ)#λ, ((A ⨂ B)#λ ⨂ C)#λ]({
        case Left(a) => Left(Left(a))
        case Right(Left(b)) => Left(Right(b))
        case Right(Right(c)) => Right(c)
      }, {
        case Left(Left(a)) => Left(a)
        case Left(Right(b)) => Right(Left(b))
        case Right(c) => Right(Right(c))
      })

    final def commute[A[_], B[_]]: IsoK[(A ⨂ B)#λ, (B ⨂ A)#λ] =
      total[(A ⨂ B)#λ, (B ⨂ A)#λ]({
        case Left(a) => Right(a)
        case Right(b) => Left(b)
      },
        {
          case Right(a) => Left(a)
          case Left(b) => Right(b)
        })

    final def unit[A[_]]: IsoK[A, (A ⨂ Id)#λ] =
      total[A, (A ⨂ Id)#λ](
        { case a => Left(a) },
        {
          case Left(a) => a
          case Right(n) => Void.absurd(n)
        })

    final def first[A[_], B[_], C[_]](iso: IsoK[A, C]): IsoK[(A ⨂ B)#λ, (C ⨂ B)#λ] =
      iso or id

    final def second[A[_], B[_], C[_]](iso: IsoK[B, C]): IsoK[(A ⨂ B)#λ, (A ⨂ C)#λ] =
      id or iso
  }
}