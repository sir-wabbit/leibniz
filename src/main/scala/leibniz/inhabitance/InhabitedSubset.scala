package leibniz
package inhabitance

final case class InhabitedSubset[A, +B](conformity: A <~< B, inhabitance: Inhabited[A])
object InhabitedSubset {

}
