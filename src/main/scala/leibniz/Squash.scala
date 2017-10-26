package leibniz


/**
  * Take two equal types `A === B` with different bounds `A >: LA <: HA`, `B >: LB <: HB`
  * and find a new type `C === A === B` that is bounded by `C >: (LA | LB) <: (HA & HB)`.
  *
  * Due to Scala2's lack of unions, the signature is a bit uglier than it could be.
  */
sealed abstract class Squash[
  LA, HA >: LA, A >: LA <: HA,
  LB >: LA <: HA, HB >: LB,
  B >: LB <: HB
] {
  type Type >: LB <: (HA with HB)
  def left: A === Type
  def right: B === Type
}
object Squash {
  private[this] final class Instance
  [LA, HA >: LA, A >: LA <: HA,
   LB >: LA <: HA, HB >: LB, B >: LB <: HB,
   T >: LB <: (HA with HB)]
  (val left: A === T, val right: B === T) extends Squash[LA, HA, A, LB, HB, B]
  {
    type Type = T
  }

  def refl[L, H >: L, A >: L <: H]: Squash[L, H, A, L, H, A] =
    witness[L, H, A, L, H, A, A](Is.refl[A], Is.refl[A])

  def witness[
   LA, HA >: LA, A >: LA <: HA,
   LB >: LA <: HA, HB >: LB, B >: LB <: HB,
   T >: LB <: (HA with HB)]
  (left: A === T, right: B === T): Squash[LA, HA, A, LB, HB, B] =
    new Instance[LA, HA, A, LB, HB, B, T](left, right)
}