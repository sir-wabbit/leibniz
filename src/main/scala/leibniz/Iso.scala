package leibniz

import cats.Functor
import cats.functor.Contravariant
import cats.functor.Invariant

import scala.{ specialized => sp }

trait Iso[A, @sp B] { ab =>
  def to(a: A): B
  def from(b: B): A

  def substCoF[F[_]](fa: F[A])(implicit F: Functor[F]): F[B] =
    F.map(fa)(to)

  def substCtF[F[_]](fa: F[A])(implicit F: Contravariant[F]): F[B] =
    F.contramap(fa)(from)

  def substF[F[_]](fa: F[A])(implicit F: Invariant[F]): F[B] =
    F.imap(fa)(to)(from)

  def andThen[C](bc: Iso[B, C]): Iso[A, C] = new Iso[A, C] {
    def to(a: A): C = bc.to(ab.to(a))
    def from(c: C): A = ab.from(bc.from(c))
  }

  def compose[Z](za: Iso[Z, A]): Iso[Z, B] = za.andThen(ab)

  def lift[F[_]](implicit F: Functor[F]): Iso[F[A], F[B]] = new Iso[F[A], F[B]] {
    def to(fa: F[A]): F[B] = F.map(fa)(ab.to)
    def from(fb: F[B]): F[A] = F.map(fb)(ab.from)
  }

  def flip: Iso[B, A] = new Iso[B, A] {
    def to(b: B): A = ab.from(b)
    def from(a: A): B = ab.to(a)
    override val flip: Iso[A, B] = ab
  }
}
object Iso {
  def apply[A, B](implicit ab: Iso[A, B]): Iso[A, B] = ab

  final case class Refl[A]() extends Iso[A, A] {
    def to(a: A): A = a
    def from(b: A): A = b
  }

  private[this] final val anyIso: Iso[Any, Any] = Refl[Any]()
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  implicit def id[A]: Iso[A, A] = anyIso.asInstanceOf[Iso[A, A]]

  implicit def flip[A, B](implicit ab: Iso[A, B]): Iso[B, A] = ab.flip
}