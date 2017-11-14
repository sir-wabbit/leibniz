package leibniz
package inhabitance

import leibniz.{<~<, ===}

sealed trait Proposition1[A] {
  def isProposition: Proposition[A]
  def toContractible(proof: Inhabited[A]): Contractible[A]
  def proved(proof: Inhabited[A]): A
}
object Proposition1 {

}