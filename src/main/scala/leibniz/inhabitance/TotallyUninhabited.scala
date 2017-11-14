package leibniz.inhabitance

import cats.~>

sealed abstract class TotallyUninhabited[F[_]] {
  def proof[A]: Uninhabited[F[A]]

  def contramapK[G[_]](f: G ~> F): TotallyUninhabited[G]
}
object TotallyUninhabited {

}