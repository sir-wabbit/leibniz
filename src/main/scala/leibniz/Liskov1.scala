package leibniz

sealed abstract class Liskov1[-L, +H >: L, A >: L <: H, B >: L <: H] { ab =>
  import Liskov1._

  type Lower >: L <: (B with Upper)
  type Upper >: A <: H

  def lower: Leibniz[L, H, A, Lower]
  def upper: Leibniz[L, H, B, Upper]

  def loosen: Liskov[L, H, A, B] = {
    type f[x >: L <: H, y >: L <: H] = Liskov[L, H, x, y]
    Leibniz.pair(lower.flip, upper.flip).subst[f](
      Liskov.reify[L, H, Lower, Upper])
  }

  def substCt[F[-_ >: L <: H]](fb: F[B]): F[A] =
    lower.flip.subst[F](upper.subst[F](fb) : F[Lower])

  def substCo[F[+_ >: L <: H]](fa: F[A]): F[B] =
    upper.flip.subst[F](lower.subst[F](fa) : F[Upper])

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    */
  def coerce(a: A): B = {
    type f[+x >: L <: H] = x
    substCo[f](a)
  }

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    */
  final def andThen[L2 <: L, H2 >: H, C >: L2 <: H2]
  (bc: Liskov1[L2, H2, B, C]): Liskov1[L2, H2, A, C] =
    Liskov1.compose[L2, H2, A, B, C](bc, ab)

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[L2 <: L, H2 >: H, Z >: L2 <: H2]
  (za: Liskov1[L2, H2, Z, A]): Liskov1[L2, H2, Z, B] =
    za.andThen(ab)

//  /**
//    * Given `A <~< B` we can prove that `F[A] <~< F[B]` for any
//    * covariant `F[+_]`.
//    *
//    * @see [[liftCt]]
//    */
//  final def liftCo[F[+_]]: F[A] <~< F[B] = {
//    type f[-α] = F[α] <~< F[B]
//    substCt[f](refl)
//  }
//
//  /**
//    * Given `A <~< B` we can prove that `F[B] <~< F[B]` for any
//    * contravariant `F[-_]`.
//    *
//    * @see [[liftCo]]
//    */
//  final def liftCt[F[-_]]: F[B] <~< F[A] = {
//    type f[+α] = F[α] <~< F[A]
//    substCo[f](refl)
//  }

  /**
    * A value of `A <~< B` is always sufficient to produce a similar [[<:<]]
    * value.
    */
  final def toPredef: A <:< B = {
    type f[-α] = α <:< B
    substCt[f](implicitly[B <:< B])
  }
}
object Liskov1 {
  final case class Refl[A]() extends Liskov1[A, A, A, A] {
    type Lower = A
    type Upper = A
    def lower: Leibniz[A, A, A, A] = Leibniz.refl[A]
    def upper: Leibniz[A, A, A, A] = Leibniz.refl[A]
  }
  private[this] val anyRefl: Liskov1[Any, Any, Any, Any] = Refl[Any]()

  /**
    * Unsafe coercion between types. `unsafeForce` abuses `asInstanceOf` to
    * explicitly coerce types. It is unsafe.
    */
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def unsafeForce[L, H >: L, A >: L <: H, B >: L <: H]: Liskov1[L, H, A, B] =
    anyRefl.asInstanceOf[Liskov1[L, H, A, B]]

  /**
    * Subtyping relation is reflexive.
    */
  def refl[A]: Liskov1[A, A, A, A] = unsafeForce[A, A, A, A]

  def proved[
    L, H >: L,
    A >: L <: H, B >: L <: H,
    A1 >: L <: (B with B1),
    B1 >: A <: H
  ](a: Leibniz[L, H, A, A1], b: Leibniz[L, H, B, B1]): Liskov1[L, H, A, B] =
    new Liskov1[L, H, A, B] {
      type Upper = B1
      type Lower = A1
      def lower: Leibniz[L, H, A, A1] = a
      def upper: Leibniz[L, H, B, B1] = b
    }

  implicit def fix[L, H >: L, A >: L <: H, B >: L <: H]
  (implicit ab: Liskov[L, H, A, B]): Liskov1[L, H, A, B] = ab.fix[L, H, A, B]

  /**
    * Reify Scala's subtyping relationship into an evidence value.
    */
  def reify[L, H >: L, A >: L <: (H with B), B >: L <: H]: Liskov1[L, H, A, B] =
    Liskov.reify[L, H, A, B].fix[L, H, A, B]

  /**
    * Subtyping is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[Liskov1.compose]]
    * @see [[Liskov1.andThen]]
    */
  def compose[L, H >: L, A >: L <: H, B >: L <: H, C >: L <: H]
  (bc: Liskov1[L, H, B, C], ab: Liskov1[L, H, A, B]): Liskov1[L, H, A, C] = {
    type f[+x >: L <: H] = Liskov[L, H, A, x]
    bc.loosen.substCo[f](ab.loosen).fix
  }

  /**
    * Subtyping is antisymmetric in theory (and in Dotty). Notice that this is
    * not true in Scala until [[https://issues.scala-lang.org/browse/SI-7278
    * SI-7278]] is fixed, so this function is marked unsafe.
    */
  def bracket[L, H >: L, A >: L <: H, B >: L <: H]
  (f: Liskov1[L, H, A, B], g: Liskov1[L, H, B, A]): Leibniz[L, H, A, B] =
    Leibniz.unsafeForce[L, H, A, B]

  /**
    * It can be convenient to convert a [[<:<]] value into a `<~<` value.
    * This is not strictly valid as while it is almost certainly true that
    * `A <:< B` implies `A <~< B` it is not the case that you can create
    * evidence of `A <~< B` except via a coercion. Use responsibly.
    */
  def fromPredef[L, H >: L, A >: L <: H, B >: L <: H](eq: A <:< B): Liskov1[L, H, A, B] =
    unsafeForce[L, H, A, B]
}