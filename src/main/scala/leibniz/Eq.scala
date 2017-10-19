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

trait EqLowerPriority {
  implicit val optionVoid: Eq[Option[Void]] = new Eq[Option[Void]] {
    override def eqv(x: Option[Void], y: Option[Void]): Boolean =
      (x, y) match {
        case (null, null) => true
        case (None, None) => true
        case (Some(x), Some(y)) => Void.absurd(x)
        case _ => false
      }
  }
}

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
object Eq extends EqLowerPriority {
  import java.lang.Float.floatToRawIntBits
  import java.lang.Double.doubleToRawLongBits

  def apply[A](implicit A: Eq[A]): Eq[A] = A

  private[this] final object ReferenceEq extends Eq[AnyRef] {
    override def eqv(x: AnyRef, y: AnyRef): Boolean = x eq y
  }

  private[this] final object SingletonEq extends Eq[Singleton] {
    override def eqv(x: Singleton, y: Singleton): Boolean = {
      if (x == null) y == null
      else if (x.isInstanceOf[Boolean]) x.equals(y)
      else if (x.isInstanceOf[Byte]) x.equals(y)
      else if (x.isInstanceOf[Short]) x.equals(y)
      else if (x.isInstanceOf[Int]) x.equals(y)
      else if (x.isInstanceOf[Long]) x.equals(y)
      else if (x.isInstanceOf[Char]) x.equals(y)
      else if (x.isInstanceOf[Unit]) x == y
      else if (x.isInstanceOf[Float]) {
        if (y.isInstanceOf[Float])
          floatToRawIntBits(x.asInstanceOf[Float]) == floatToRawIntBits(y.asInstanceOf[Float])
        else false
      } else if (x.isInstanceOf[Double]) {
        if (y.isInstanceOf[Double])
          doubleToRawLongBits(x.asInstanceOf[Double]) == doubleToRawLongBits(y.asInstanceOf[Double])
        else false
      } else if (x.isInstanceOf[String]) x.equals(y)
      else if (x.isInstanceOf[Symbol]) x.equals(y)
      else x.asInstanceOf[AnyRef].eq(y.asInstanceOf[AnyRef])
    }
  }

  private[this] final object UniversalEq extends Eq[Any] {
    override def eqv(x: Any, y: Any): Boolean = x match {
      case _: y.type => true
      case _ => false
    }
  }

  def universalEq[A]: Eq[A] = UniversalEq.asInstanceOf[Eq[A]]
  def referenceEq[A <: AnyRef]: Eq[A] = ReferenceEq.asInstanceOf[Eq[A]]
  def singletonEq[A <: Singleton]: Eq[A] = SingletonEq.asInstanceOf[Eq[A]]

  implicit val eqBool:   Eq[Boolean] = universalEq[Boolean]
  implicit val eqByte:   Eq[Byte]    = universalEq[Byte]
  implicit val eqShort:  Eq[Short]   = universalEq[Short]
  implicit val eqInt:    Eq[Int]     = universalEq[Int]
  implicit val eqLong:   Eq[Long]    = universalEq[Long]
  implicit val eqChar:   Eq[Char]    = universalEq[Char]
  implicit val eqString: Eq[String]  = universalEq[String]

  implicit val eqFloat:  Eq[Float]   = new Eq[Float] {
    override def eqv(x: Float, y: Float): Boolean =
      floatToRawIntBits(x) == floatToRawIntBits(y)
  }

  implicit val eqDouble: Eq[Double]  = new Eq[Double] {
    override def eqv(x: Double, y: Double): Boolean =
      doubleToRawLongBits(x) == doubleToRawLongBits(y)
  }

  implicit val eqUnit:   Eq[Unit]    = new Eq[Unit] {
    override def eqv(x: Unit, y: Unit): Boolean =
      true
  }

  implicit def option[T](implicit A: Eq[T]): Eq[Option[T]] = new Eq[Option[T]] {
    override def eqv(x: Option[T], y: Option[T]): Boolean =
      (x, y) match {
        case (null, null) => true
        case (None, None) => true
        case (Some(x), Some(y)) => A.eqv(x, y)
        case _ => false
      }
  }

  implicit def pair[A, B](implicit A: Eq[A], B: Eq[B]): Eq[(A, B)] = new Eq[(A, B)] {
    override def eqv(x: (A, B), y: (A, B)): Boolean =
      (x, y) match {
        case (null, null) => true
        case ((x1, x2), (y1, y2)) => A.eqv(x1, y1) && B.eqv(x2, y2)
        case _ => false
      }
  }

  implicit def either[A, B](implicit A: Eq[A], B: Eq[B]): Eq[Either[A, B]] = new Eq[Either[A, B]] {
    override def eqv(x: Either[A, B], y: Either[A, B]): Boolean =
      (x, y) match {
        case (null, null) => true
        case (Left(x), Left(y)) => A.eqv(x, y)
        case (Right(x), Right(y)) => B.eqv(x, y)
        case _ => false
      }
  }
}
