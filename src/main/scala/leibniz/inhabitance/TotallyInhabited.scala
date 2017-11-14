package leibniz.inhabitance

import cats.data.Tuple2K
import cats.~>

trait TotallyInhabited[F[_]] {
  def proof[A]: Inhabited[F[A]]

  def mapK[G[_]](f: F ~> G): TotallyInhabited[G]

  def zipK[G[_]](g: TotallyInhabited[G]): TotallyInhabited[Tuple2K[F, G, ?]]
}
object TotallyInhabited {

}