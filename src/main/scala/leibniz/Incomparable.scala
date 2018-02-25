package leibniz

import leibniz.inhabitance.Proposition

final case class Incomparable[A, B](notLessOrEqual: ¬[A <~< B], notGreaterOrEqual: ¬[B <~< A]) { ab =>
  import Incomparable._

  def notEqual   :   A =!= B  = WeakApart.witness(equal => notLessOrEqual(equal.toAs))
  def notLess    : ¬[A </< B] = ineq => notLessOrEqual(ineq.conformity)
  def notGreater : ¬[B </< A] = ineq => notGreaterOrEqual(ineq.conformity)

  def lift[F[_]](implicit F: variance.Injective[F]): F[A] >~< F[B] =
    F.incomparable[A, B](ab)

  def flip: B >~< A = witness(notGreaterOrEqual, notLessOrEqual)
}
object Incomparable {
  def witness[A, B](notBelow: ¬[A <~< B], notAbove: ¬[B <~< A]): Incomparable[A, B] =
    new Incomparable[A, B](notBelow, notAbove)

  /**
    * a ≸ b ⟺ ¬(a ~ b) ⋀ ¬(a < b) ⋀ ¬(b < a)
    */
  def witness1[A, B](notEqual: A =!= B, notLess: ¬[A </< B], notGreater: ¬[B </< A]): A >~< B =
    notEqual.decompose.map {
      case Right(ncmp) => ncmp
      case Left(Right(lt)) => notLess(lt)
      case Left(Left(gt)) => notGreater(gt)
    }.proved

  /**
    * ¬(a ≸ b)
    * ⟺ ¬(¬(a ~ b) ⋀ ¬(a < b) ⋀ ¬(b < a))
    * ⟺ a ~ b ⋁ a < b ⋁ b < a
    * ⟺ a ≤ b ⋁ b ≤ b
    */
  def witnessNot[A, B](ev: ¬¬[(B <~< A) Either (A <~< B)]): ¬[A >~< B] = ab => ev.run {
    case Right(below) => ab.notLessOrEqual(below)
    case Left(above) => ab.notGreaterOrEqual(above)
  }

  def irreflexive[A](ev: A >~< A): Void =
    ev.notEqual(Is.refl)

  implicit def proposition[A, B]: Proposition[Incomparable[A, B]] =
    (Proposition[¬[A <~< B]] zip Proposition[¬[B <~< A]]).isomap(Iso.unsafe(
      p => witness(p._1, p._2),
      p => (p.notLessOrEqual, p.notGreaterOrEqual)
    ))
}