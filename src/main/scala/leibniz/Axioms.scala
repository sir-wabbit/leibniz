package leibniz

import leibniz.internal.Unsafe

/**
  * These are some non-trivial axioms that the library uses.
  */
@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
object Axioms {
  /**
    *
    */
  def predefEq[A, B](ab: A =:= B): A === B =
    Unsafe.is[A, B]

  /**
    *
    */
  def predefConformity[A, B](eq: A <:< B): A <~< B =
    Unsafe.as[A, B]

  def isConsistency[A, B](ab: ((A === B) => Void) => Void): A === B =
    Unsafe.is[A, B]

  def asConsistency[A, B](ab: ((A <~< B) => Void) => Void): A <~< B =
    Unsafe.as[A, B]

  def leibnizConsistency[L, H >: L, A >: L <: H, B >: L <: H](ab: (Leibniz[L, H, A, B] => Void) => Void): Leibniz[L, H, A, B] =
    Leibniz.refl[A].asInstanceOf[Leibniz[L, H, A, B]]

  def liskovConsistency[L, H >: L, A >: L <: H, B >: L <: H](ab: (Liskov[L, H, A, B] => Void) => Void): Liskov[L, H, A, B] =
    Liskov.refl[A].asInstanceOf[Liskov[L, H, A, B]]

  def isKConsistency[A[_], B[_]](ab: ((A =~= B) => Void) => Void): A =~= B =
    Unsafe.isK[A, B]

  def isFConsistency[F[X <: F[X]], A <: F[A], B <: F[B]](ab: (IsF[F, A, B] => Void) => Void): IsF[F, A, B] =
    Unsafe.isF[F, A, B]

  /**
    * Subtyping is antisymmetric.
    */
  def bracket[A, B](f: A <~< B, g: B <~< A): A === B =
    Unsafe.is[A, B]

  /**
    * ∀ a b x y. (f a = f b) ∧ ¬(a = b) => f x = f y
    */
  def phParametricity[F[_], A, B, X, Y](fab: F[A] === F[B], ab: (A === B) => Void): F[X] === F[Y] =
    Unsafe.is[F[X], F[Y]]

  /**
    * (a < b) ∧ (f a <= f b) => ∀ x y. (x <= y) => (f x <= f y)
    */
  def cvParametricity[F[_], A, B, X, Y]
  (ab: (A === B) => Void, p: A <~< B, q: F[A] <~< F[B], r: X <~< Y): F[X] <~< F[Y] =
    Unsafe.as[F[X], F[Y]]

  /**
    * (a < b) ∧ (f b <= f a) => ∀ x y. (x <= y) => (f y <= f x)
    */
  def ctParametricity[F[_], A, B, X, Y]
  (ab: (A === B) => Void, p: A <~< B, q: F[B] <~< F[A], r: X <~< Y): F[Y] <~< F[X] =
    Unsafe.as[F[Y], F[X]]

  /**
    * (a < b) ∧ (f a >< f b) => ∀ x y. (x < y) => (f x >< f y)
    */
  def invParametricity[F[_], A, B, X, Y]
  (ab: A </< B, fab: F[A] >~< F[B], nxy: X =!= Y): F[X] >~< F[Y] =
    Unsafe.incomparable[F[X], F[Y]]

  /**
    * a ≸ b ⋀ f a ≠ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y
    */
  def parametricity1[F[_], A, B, X, Y](ab: A >~< B, nfxy: F[A] =!= F[B], nxy: X =!= Y): F[X] >~< F[Y] =
    Unsafe.incomparable[F[X], F[Y]]

  /**
    * (∀ x . f x = g x) => f = g
    */
  def tcExtensionality[F[_], G[_]]: TCExtensionality[F, G] = new TCExtensionality[F, G]

  final class TCExtensionality[F[_], G[_]](val b: Boolean = true) extends AnyVal {
    type T
    def apply(uv: F[T] === G[T]): F =~= G = Unsafe.isK[F, G]

    def applyT(f: TypeHolder[T] => (F[T] === G[T])): F =~= G =
      apply(f(TypeHolder[T]))
  }

  /**
    *
    */
  def fBounded[F[X <: F[X]], A <: F[A], B <: F[B], G[X <: F[X]]](eq: A === B, fa: G[A]): G[B] =
    Unsafe.is[G[A], G[B]].apply(fa)

  /**
    *
    */
  def bounded[L, H >: L, A >: L <: H, B >: L <: H, F[_ >: L <: H]](eq: A === B, fa: F[A]): F[B] =
    Unsafe.is[F[A], F[B]].apply(fa)

  /**
    * Take two equal types `A === B` with different bounds `A >: LA <: HA`, `B >: LB <: HB`
    * and find a new type `C === A === B` that is bounded by `C >: (LA | LB) <: (HA & HB)`.
    *
    * Due to Scala2's lack of unions, the signature is a bit uglier than it could be.
    */
  def squash[
    LA, HA >: LA, A >: LA <: HA,
    LB >: LA <: HA, HB >: LB, B >: LB <: HB
  ] (eq: A === B): Squash[LA, HA, A, LB, HB, B] =
    Squash.refl[LA, HA, A].asInstanceOf[Squash[LA, HA, A, LB, HB, B]]
}
