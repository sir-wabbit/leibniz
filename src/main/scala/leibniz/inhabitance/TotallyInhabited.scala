package leibniz
package inhabitance

//import cats.~>

sealed abstract class TotallyInhabited[F[_]] {
  def proof[A]: Inhabited[F[A]]

//  def mapK[G[_]](f: F ~> G): TotallyInhabited[G]

  def zipK[G[_]](g: TotallyInhabited[G]): TotallyInhabited[λ[x => (F[x], G[x])]]
}
object TotallyInhabited {

}