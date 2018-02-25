package leibniz
package internal

@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
final case class Unsafe private (value: Unsafe.type) extends AnyVal {
  @inline def not[A]: A => Void = _ => ???
  @inline def is[A, B]: A === B = Is.refl[A].asInstanceOf[A === B]
  @inline def weakApart[A, B]: WeakApart[A, B] = WeakApart(not[A === B])
  @inline def apart[A, B](A: TypeId[A], B: TypeId[B]): Apart[A, B] = Apart.witness(weakApart[A, B], A, B)

  @inline def isK[A[_], B[_]]: A =~= B = IsK.refl[A].asInstanceOf[A =~= B]
  @inline def isF[F[X <: F[X]], A <: F[A], B <: F[B]]: IsF[F, A, B] = IsF.refl[F, A].asInstanceOf[IsF[F, A, B]]
  @inline def as[A, B]: A <~< B = As.refl[A].asInstanceOf[A <~< B]
  @inline def strictAs[A, B]: A </< B = StrictAs.bottomTop.asInstanceOf[A </< B]
  @inline def incomparable[A, B]: A >~< B = Incomparable(not[A <~< B], not[B <~< A])
}

@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
object Unsafe {
  implicit val unsafe: Unsafe = Unsafe(this)
  implicit def fromCompanion(u: Unsafe.type): Unsafe = Unsafe(u)
}
