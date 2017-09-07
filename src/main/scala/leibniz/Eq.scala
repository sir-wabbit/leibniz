package leibniz

import scala.{specialized => sp}

trait Eq[@sp -A] extends Any with Serializable {
  /**
    * Returns `true` if `x` and `y` are equal, `false` otherwise.
    */
  def eqv(x: A, y: A): Boolean

  /**
    * Returns `false` if `x` and `y` are equal, `true` otherwise.
    */
  def neqv(x: A, y: A): Boolean = !eqv(x, y)

  def eqProof(x: A, y: A): Option[x.type === y.type] =
    if (eqv(x, y)) Some(Is.unsafeForce[x.type, y.type]) else None
}

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
object Eq {
  private[this] final class UniversalEq extends Eq[Any] {
    override def eqv(x: Any, y: Any): Boolean = x match {
      case _: y.type => true
      case _ => false
    }
  }

  def fromUniversalEq[A]: Eq[A] = new UniversalEq

  implicit val eqUnit:   Eq[Unit]    = (_: Unit, _: Unit) => true
  implicit val eqBool:   Eq[Boolean] = fromUniversalEq[Boolean]
  implicit val eqByte:   Eq[Byte]    = fromUniversalEq[Byte]
  implicit val eqShort:  Eq[Short]   = fromUniversalEq[Short]
  implicit val eqInt:    Eq[Int]     = fromUniversalEq[Int]
  implicit val eqLong:   Eq[Long]    = fromUniversalEq[Long]
  implicit val eqFloat:  Eq[Float]   = (x: Float, y: Float) =>
    java.lang.Float.floatToRawIntBits(x) == java.lang.Float.floatToRawIntBits(y)
  implicit val eqDouble: Eq[Double]  = (x: Double, y: Double) =>
    java.lang.Double.doubleToRawLongBits(x) == java.lang.Double.doubleToRawLongBits(y)
  implicit val eqString: Eq[String]  = (x: String, y: String) =>
    x.equals(y)

  @SuppressWarnings(Array("org.wartremover.warts.OptionPartial"))
  implicit def eqOption[A](implicit A: Eq[A]): Eq[Option[A]] = (x: Option[A], y: Option[A]) =>
    x match {
      case None => y.isEmpty
      case Some(x) => y.isDefined && A.eqv(y.get, x)
    }
}
