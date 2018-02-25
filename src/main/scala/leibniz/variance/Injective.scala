package leibniz
package variance

import leibniz.inhabitance.{Inhabited, Proposition, Uninhabited}

trait Injective[F[_]] { F =>
  import Injective._

  /**
    * The function f is said to be injective provided that for all a and b in X,
    * whenever f(a) = f(b), then a = b.
    */
  def apply[A, B](implicit ev: F[A] === F[B]): A === B

  /**
    * Constant type constructors are not injective.
    */
  def notConstant(cF: Constant[F]): Void =
    F(cF[Unit, Void]).coerce(())

  def incomparable[A, B](ev: A >~< B): F[A] >~< F[B] =
    Parametric[F].liftInc[A, B, A, B](ev, contrapositive(ev.notEqual), ev.notEqual)

  /**
    * F is injective if and only if, given any G, H whenever F ∘ G = F ∘ H, then G = H.
    * In other words, injective type constructors are precisely the monomorphisms in the category
    * of types and type constructors.
    */
  def monomorphism[G[_], H[_]](p: λ[x => F[G[x]]] =~= λ[x => F[H[x]]]): G =~= H =
    Axioms.tcExtensionality[G, H].applyT { t =>
      type T = t.Type
      F[G[T], H[T]](p.lower[λ[x[_] => x[T]]])
    }

  /**
    * If A ≠ B, then F[A] ≠ F[B].
    */
  def contrapositive[A, B](ev: A =!= B): F[A] =!= F[B] =
    WeakApart.witness[F[A], F[B]] { fab => ev.apply(F(fab)) }

  /**
    * If G ∘ F is injective, then F is injective (but G need not be).
    */
  def decompose[G[_], H[_]](implicit p: F =~= λ[x => G[H[x]]]): Injective[H] = {
    val GH: Injective[λ[x => G[H[x]]]] = p.subst[Injective](F)

    new Injective[H] {
      override def apply[A, B](implicit ev: H[A] === H[B]): A === B =
        GH(ev.lift[G])

      override def monomorphism[I[_], J[_]](p: λ[x => H[I[x]]] =~= λ[x => H[J[x]]]): I =~= J = {
        type f[x[_], a] = G[x[a]]
        val q : λ[x => G[H[I[x]]]] =~= λ[x => G[H[J[x]]]] = p.lift[f]
        GH.monomorphism[I, J](q)
      }
    }
  }

  /**
    * If F and G are both injective, then F ∘ G is injective.
    */
  def compose[G[_]](implicit G: Injective[G]): Injective[λ[x => F[G[x]]]] =
    new Compose[F, G](F, G)

  /**
    * If F and G are both injective, then G ∘ F is injective.
    */
  def andThen[G[_]](implicit G: Injective[G]): Injective[λ[x => G[F[x]]]] =
    new Compose[G, F](G, F)

//  /**
//    * Classical proof that
//    * injective f ⟺ invariant f ⋁ strictly-contravariant f ⋁ strictly-covariant f
//    */
//  def decompose: ¬¬[StrictlyContravariant[F] Either StrictlyCovariant[F] Either Invariant[F]] =
//    Inhabited.lem[StrictlyCovariant[F]].flatMap {
//      case Right(cv) => Inhabited.value(Left(Right(cv)))
//      case Left(notCV) =>
//        Inhabited.lem[StrictlyContravariant[F]].map {
//          case Right(ct) => Left(Left(ct))
//          case Left(notCT) => Right(Incomparable(notCV, notCT))
//        }
//    }
}

//trait InjectiveLowerPriority {
//  implicit def mkInjective[F[_]]: Injective[F] =
//    macro internal.MacroUtil.mkInjective[F]
//}

object Injective {
  def apply[F[_]](implicit F: Injective[F]): Injective[F] = F

  implicit def witness[F[_]](implicit fnab: F[Void] =!= F[Any]): Injective[F] =
    witness1[F, Void, Any](fnab)

  def witness1[F[_], A, B](fnab: F[A] =!= F[B]): Injective[F] = new Injective[F] {
    override def apply[X, Y](implicit ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj[A, B, X, Y](fnab, ev)
  }

  def witness2[F[_], G[_], A, B](x: G[F[A]], y: G[F[B]] => Void): Injective[F] =
    witness1[F, A, B](WeakApart { ab =>
      type f[x] = G[x]
      y(ab.subst[f](x))
    })

  def witness3[F[_], G[_], A, B](x: Inhabited[G[F[A]]], y: Uninhabited[G[F[B]]]): Injective[F] =
    witness1[F, A, B](WeakApart { ab =>
      type f[x] = Inhabited[G[x]]
      ab.subst[f](x).notUninhabited(y)
    })

  def viaRetraction[F[_], R[_ <: F[_]]](retraction: λ[x => R[F[x]]] =~= λ[x => x]): Injective[F] =
    witness1[F, Void, Unit](WeakApart { ab =>
      val p = Leibniz.fromIs[Nothing, F[_], F[Void], F[Unit]](ab)
      val r: R[F[Unit]] === R[F[Void]] = p.lift[Nothing, Any, R].toIs.flip
      val q: R[F[Void]] === Void = retraction.lower[λ[x[_] => x[Void]]]
      val s: Unit === R[F[Unit]] = retraction.flip.lower[λ[x[_] => x[Unit]]]

      (s andThen r andThen q).coerce(())
    })

//  implicit val id: Injective[λ[X => X]] =
//    witness[λ[X => X]](Void.isNotAny)

  final case class Compose[F[_], G[_]](F: Injective[F], G: Injective[G]) extends Injective[λ[x => F[G[x]]]] {
    override def apply[A, B](implicit ev: F[G[A]] === F[G[B]]): A === B =
      G[A, B](F[G[A], G[B]](ev))
  }

  implicit def proposition[F[_]]: Proposition[Injective[F]] =
    (A: ¬¬[Injective[F]]) => new Injective[F] {
      override def apply[A, B](implicit ev: F[A] === F[B]): A === B = A.map(_[A, B]).proved
    }
}