package leibniz.inhabitance

import cats.~>

trait TotallyUninhabited[F[_]] {
  def proof[A]: Uninhabited[F[A]]

  def contramapK[G[_]](f: G ~> F): TotallyUninhabited[G]
}
object TotallyUninhabited {

}