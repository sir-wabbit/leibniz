package leibniz

import leibniz.internal.Unsafe

sealed abstract class StrictAs[-A, +B] { ab =>
  import StrictAs._

  def inequality[A1 <: A, B1 >: B]: A1 =!= B1

  def conformity: A <~< B

  def contradicts(ba: StrictAs[B, A]): Void =
    inequality[A, B].contradicts(Axioms.bracket(ab.conformity, ba.conformity)(Unsafe.unsafe))

  /**
    * Substitution into a covariant context.
    *
    * @see [[substCt]]
    */
  def substCo[F[+_]](fa: F[A]): F[B] =
    conformity.substCo[F](fa)

  /**
    * Substitution into a contravariant context.
    *
    * @see [[substCo]]
    */
  def substCt[F[-_]](fb: F[B]): F[A] =
    conformity.substCt[F](fb)

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    *
    * @see [[coerce]]
    */
  final def apply(a: A): B =
    coerce(a)

  def andThen[A1 <: A, C](bc: StrictAs[B, C]): StrictAs[A1, C] =
    bc.conformity.substCo[StrictAs[A1, +?]](ab)

  def compose[Z, B1 >: B](za: StrictAs[Z, A]): StrictAs[Z, B1] =
    za andThen ab

  def andThenNS[A1 <: A, C](bc: As[B, C]): StrictAs[A1, C] =
    bc.substCo[StrictAs[A1, +?]](ab)

  def composeNS[Z, B1 >: B](za: As[Z, A]): StrictAs[Z, B1] =
    za.substCt[StrictAs[-?, B1]](ab)

  /**
    * Substitution on identity brings about a direct coercion function
    * of the same form that [[<:<]] provides.
    *
    * @see [[apply]]
    */
  final def coerce(a: A): B = {
    type f[+x] = x
    substCo[f](a)
  }

  /**
    * Given `A <~< B` we can prove that `F[A] <~< F[B]` for any
    * covariant `F[+_]`.
    *
    * @see [[liftCtNS]]
    */
  final def liftCoNS[F[+_]]: F[A] <~< F[B] = {
    type f[+x] = F[A] <~< F[x]
    substCo[f](As.refl[F[A]])
  }

  /**
    * Given `A <~< B` we can prove that `F[A] <~< F[B]` for any
    * contravariant `F[-_]`.
    *
    * @see [[liftCoNS]]
    */
  final def liftCtNS[F[-_]]: F[B] <~< F[A] = {
    type f[+x] = F[x] <~< F[A]
    substCo[f](As.refl)
  }
}
object StrictAs {
  private[this] final class Witness[A, B](val nab: A =!= B, val conformity: A <~< B) extends StrictAs[A, B] {
    def inequality[A1 <: A, B1 >: B]: A1 =!= B1 =
      WeakApart.witness { a1b1 =>
        val nc: B1 <~< A1 = a1b1.flip.toAs
        nab.contradicts(Axioms.bracket(conformity, nc : As[B, A])(Unsafe.unsafe))
      }
  }

  def witness[A, B](implicit nab: A =!= B, conformity: A <~< B): StrictAs[A, B] =
    new Witness[A, B](nab, conformity)
}