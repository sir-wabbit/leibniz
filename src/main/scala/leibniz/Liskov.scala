package leibniz

import Liskov.id

/**
  * Liskov substitutability: A better `<:<`.
  *
  * `Liskov[A, B]` witnesses that `A` can be used in any negative context
  * that expects a `B`. (e.g. if you could pass an `A` into any function
  * that expects a `B`.)
  *
  * @see [[<~<]] `A <~< B` is a type synonym to `Liskov[A, B]`
  */
sealed abstract class Liskov[-A, +B] private[Liskov] () { ab =>
  def subst[F[-_]](fb: F[B]): F[A]

  /**
    * Substitution into a contravariant context.
    *
    * @see [[substCo]]
    */
  final def substCt[F[-_]](fb: F[B]): F[A] =
    subst[F](fb)

  /**
    * Substitution into a covariant context.
    *
    * @see [[substCt]]
    */
  final def substCo[F[+_]](fa: F[A]): F[B] = {
    type f[-α] = F[α] => F[B]
    substCt[f](identity[F[B]]).apply(fa)
  }

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    *
    * @see [[coerce]]
    */
  final def apply(a: A): B =
    coerce(a)

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    */
  final def andThen[C](bc: B <~< C): A <~< C = {
    type f[-α] = α <~< C
    ab.substCt[f](bc)
  }

  /**
    * Subtyping is transitive and its witnesses can be composed in a
    * chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[Z](za: Z <~< A): Z <~< B =
    za.andThen(ab)

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    *
    * @see [[apply]]
    */
  final def coerce(a: A): B =
    substCo[λ[`+α` => α]](a)

  /**
    * Given `A <~< B` we can prove that `F[A] <~< F[B]` for any
    * covariant `F[+_]`.
    *
    * @see [[liftCt]]
    */
  final def liftCo[F[+_]]: F[A] <~< F[B] = {
    type f[-α] = F[α] <~< F[B]
    substCt[f](id)
  }

  /**
    * Given `A <~< B` we can prove that `F[B] <~< F[B]` for any
    * contravariant `F[-_]`.
    *
    * @see [[liftCo]]
    */
  final def liftCt[F[-_]]: F[B] <~< F[A] = {
    type f[+α] = F[α] <~< F[A]
    substCo[f](id)
  }

  /**
    * A value of `A <~< B` is always sufficient to produce a similar [[<:<]]
    * value.
    */
  final def toPredef: A <:< B = {
    type f[-α] = α <:< B
    substCt[f](implicitly[B <:< B])
  }
}

object Liskov {
  private[this] final case class Refl[A]() extends Liskov[A, A] {
    def subst[F[-_]](fa: F[A]): F[A] = fa
  }
  private[this] val anyRefl: Any <~< Any = Refl[Any]()

  /**
    * Unsafe coercion between types. `unsafeForce` abuses `asInstanceOf` to
    * explicitly coerce types. It is unsafe.
    */
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def unsafeForce[A, B]: A <~< B =
    anyRefl.asInstanceOf[A <~< B]

  /**
    * Subtyping relation is reflexive.
    */
  def id[A]: A <~< A = unsafeForce[A, A]

  /**
    * Reify Scala's subtyping relationship into an evidence value.
    */
  def reify[A, B >: A]: A <~< B = id

  /**
    * Subtyping is antisymmetric in theory (and in Dotty). Notice that this is
    * not true in Scala until [[https://issues.scala-lang.org/browse/SI-7278
    * SI-7278]] is fixed, so this function is marked unsafe.
    */
  def unsafeBracket[A, B, C](f: A <~< B, g: B <~< A): A === B =
    Leibniz.unsafeForce[A, B]

  /**
    * It can be convenient to convert a [[<:<]] value into a `<~<` value.
    * This is not strictly valid as while it is almost certainly true that
    * `A <:< B` implies `A <~< B` it is not the case that you can create
    * evidence of `A <~< B` except via a coercion. Use responsibly.
    */
  def unsafeFromPredef[A, B](eq: A <:< B): A <~< B =
    unsafeForce[A, B]
}