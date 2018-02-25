package leibniz

final case class Comparable[A, B](run: ¬¬[(B </< A) Either (A </< B) Either (A === B)]) {
  def notIncomparable(nc: Incomparable[A, B]): Void =
    run.run {
      case Right(ab) => nc.notEqual(ab)
      case Left(Right(ab)) => nc.notLess(ab)
      case Left(Left(ab)) => nc.notGreater(ab)
    }

  def flip: Comparable[B, A] = Comparable[B, A](run.map {
    case Right(ab) => Right(ab.flip)
    case Left(Right(ab)) => Left(Left(ab))
    case Left(Left(ab)) => Left(Right(ab))
  })
}
object Comparable {

}
