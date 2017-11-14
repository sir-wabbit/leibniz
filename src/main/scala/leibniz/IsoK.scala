package leibniz


import cats.data.Tuple2K

import scala.{specialized => sp}

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

  def and[I[_], J[_]](ij: IsoK[I, J]): IsoK[Tuple2K[A, I, ?], Tuple2K[B, J, ?]] =
    IsoK.total[Tuple2K[A, I, ?], Tuple2K[B, J, ?]](
      { case Tuple2K(a, i) => Tuple2K(ab.to(a), ij.to(i)) },
      { case Tuple2K(b, j) => Tuple2K(ab.from(b), ij.from(j)) })

//  def or[I, J](ij: Iso[I, J]): Iso[Either[A, I], Either[B, J]] =
//    Iso.total({
//      case Left(a) => Left(ab.to(a))
//      case Right(i) => Right(ij.to(i))
//    }, {
//      case Left(b) => Left(ab.from(b))
//      case Right(j) => Right(ij.from(j))
//    })
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

//  object Product {
//    type ⨂ [A, B] = (A, B)
//    type Id = Unit
//
//    final def associate[A, B, C]: Iso[A ⨂ (B ⨂ C), (A ⨂ B) ⨂ C] = total(
//      { case (a, (b, c)) => ((a, b), c) },
//      { case ((a, b), c) => (a, (b, c)) })
//
//    final def commute[A, B]: Iso[A ⨂ B, B ⨂ A] = total(
//      { case (a, b) => (b, a) },
//      { case (b, a) => (a, b) })
//
//    final def unit[A]: Iso[A, A ⨂ Id] = total(
//      { case a => (a, ()) },
//      { case (a, ()) => a })
//
//    final def first[A, B, C](iso: Iso[A, C]): Iso[A ⨂ B, C ⨂ B] =
//      iso and id
//
//    final def second[A, B, C](iso: Iso[B, C]): Iso[A ⨂ B, A ⨂ C] =
//      id and iso
//  }
//
//  object Coproduct {
//    type ⨂ [A, B] = Either[A, B]
//    type Id = Void
//
//    final def associate[A, B, C]: Iso[A ⨂ (B ⨂ C), (A ⨂ B) ⨂ C] =
//      total({
//        case Left(a) => Left(Left(a))
//        case Right(Left(b)) => Left(Right(b))
//        case Right(Right(c)) => Right(c)
//      }, {
//        case Left(Left(a)) => Left(a)
//        case Left(Right(b)) => Right(Left(b))
//        case Right(c) => Right(Right(c))
//      })
//
//    final def commute[A, B]: Iso[A ⨂ B, B ⨂ A] =
//      total({
//        case Left(a) => Right(a)
//        case Right(b) => Left(b)
//      },
//        {
//          case Right(a) => Left(a)
//          case Left(b) => Right(b)
//        })
//
//    final def unit[A]: Iso[A, A ⨂ Id] = total(
//      { case a => Left(a) },
//      {
//        case Left(a) => a
//        case Right(n) => Void.absurd(n)
//      })
//
//    final def first[A, B, C](iso: Iso[A, C]): Iso[A ⨂ B, C ⨂ B] =
//      iso or id
//
//    final def second[A, B, C](iso: Iso[B, C]): Iso[A ⨂ B, A ⨂ C] =
//      id or iso
//  }
}