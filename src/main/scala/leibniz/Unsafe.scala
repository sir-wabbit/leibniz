package leibniz

@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
final case class Unsafe private (value: Null) extends AnyVal {
  import Unsafe._

  @inline def cps[A](a: (A => Void) => Void): A = {
    val A: AnyRef = new AnyRef()

    try a(a => throw Return[A](A, a)) catch {
      case Return(A, a) => a.asInstanceOf[A]
    }
  }

  // *
  @inline def coerceK0[A]: Unsafe.PartialK0[A] =
    Unsafe.PartialK0[A]()

  // * -> *
  @inline def coerceK1[F[_], A]: Unsafe.PartialK1[F, A] =
    Unsafe.PartialK1[F, A]()

  // * -> (* -> *)
  @inline def coerceK2_1[F[_, _], A, B]: Unsafe.PartialK2_1[F, A, B] =
    Unsafe.PartialK2_1[F, A, B]()

  // (* -> *) -> *
  @inline def coerceK2_2[F[_[_]], A[_]]: Unsafe.PartialK2_2[F, A] =
    Unsafe.PartialK2_2[F, A]()

  // * -> * -> * -> *
  @inline def coerceK3_1[F[_, _, _], A, B, C]: Unsafe.PartialK3_1[F, A, B, C] =
    Unsafe.PartialK3_1[F, A, B, C]()

  // * -> (* -> *) -> *
  @inline def coerceK3_2[F[_, _[_]], A, B[_]]: Unsafe.PartialK3_2[F, A, B] =
    Unsafe.PartialK3_2[F, A, B]()

  // (* -> *) -> * -> *
  @inline def coerceK3_3[F[_[_], _], A[_], B]: Unsafe.PartialK3_3[F, A, B] =
    Unsafe.PartialK3_3[F, A, B]()

  // (* -> * -> *) -> *
  @inline def coerceK3_4[F[_[_, _]], A[_, _]]: Unsafe.PartialK3_4[F, A] =
    Unsafe.PartialK3_4[F, A]()

  // (((* -> *) -> *) -> *)
  @inline def coerceK3_5[F[_[_[_]]], A[_[_]]]: Unsafe.PartialK3_5[F, A] =
    Unsafe.PartialK3_5[F, A]()


  // (* -> *) -> (* -> *) -> *
  @inline def coerceK4_8[F[_[_], _[_]], A[_], B[_]]: Unsafe.PartialK4_8[F, A, B] =
    Unsafe.PartialK4_8[F, A, B]()
}

@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
object Unsafe {
  implicit val unsafe: Unsafe = Unsafe(null)

  private[Unsafe] final case class PartialK0[A](b: Boolean = true) extends AnyVal {
    @inline def apply[X](fa: X): A = fa.asInstanceOf[A]
  }
  private[Unsafe] final case class PartialK1[F[_], A](b: Boolean = true) extends AnyVal {
    @inline def apply[X](fa: F[X]): F[A] = fa.asInstanceOf[F[A]]
  }
  private[Unsafe] final case class PartialK2_1[F[_, _], A, B](b: Boolean = true) extends AnyVal {
    @inline def apply[X, Y](fa: F[X, Y]): F[A, B] = fa.asInstanceOf[F[A, B]]
  }
  private[Unsafe] final case class PartialK2_2[F[_[_]], A[_]](b: Boolean = true) extends AnyVal {
    @inline def apply[X[_]](fa: F[X]): F[A] = fa.asInstanceOf[F[A]]
  }

  private[Unsafe] final case class PartialK3_1[F[_, _, _], A, B, C](b: Boolean = true) extends AnyVal {
    @inline def apply[X, Y, Z](fa: F[X, Y, Z]): F[A, B, C] = fa.asInstanceOf[F[A, B, C]]
  }
  private[Unsafe] final case class PartialK3_2[F[_, _[_]], A, B[_]](b: Boolean = true) extends AnyVal {
    @inline def apply[X, Y[_]](fa: F[X, Y]): F[A, B] = fa.asInstanceOf[F[A, B]]
  }
  private[Unsafe] final case class PartialK3_3[F[_[_], _], A[_], B](b: Boolean = true) extends AnyVal {
    @inline def apply[X[_], Y](fa: F[X, Y]): F[A, B] = fa.asInstanceOf[F[A, B]]
  }
  private[Unsafe] final case class PartialK3_4[F[_[_, _]], A[_, _]](b: Boolean = true) extends AnyVal {
    @inline def apply[X[_, _]](fa: F[X]): F[A] = fa.asInstanceOf[F[A]]
  }
  private[Unsafe] final case class PartialK3_5[F[_[_[_]]], A[_[_]]](b: Boolean = true) extends AnyVal {
    @inline def apply[X[_[_]]](fa: F[X]): F[A] = fa.asInstanceOf[F[A]]
  }

  private[Unsafe] final case class PartialK4_8[F[_[_], _[_]], A[_], B[_]](b: Boolean = true) extends AnyVal {
    @inline def apply[X[_], Y[_]](fa: F[X, Y]): F[A, B] = fa.asInstanceOf[F[A, B]]
  }

  final case class Return[A](tag: AnyRef, a: A) extends Throwable {
    override def fillInStackTrace(): Throwable = this
  }
}
