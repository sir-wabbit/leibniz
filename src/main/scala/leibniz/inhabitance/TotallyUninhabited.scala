package leibniz.inhabitance

import cats.~>

sealed abstract class TotallyUninhabited[F[_]] {
  def proof[A]: Uninhabited[F[A]]

  def contramapK[G[_]](f: G ~> F): TotallyUninhabited[G]

  def cozipK[G[_]](G: TotallyUninhabited[G]): TotallyUninhabited[λ[x => Either[F[x], G[x]]]]
}
object TotallyUninhabited {

}