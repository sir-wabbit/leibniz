package leibniz

import leibniz.internal.{Murmur3, Unsafe}

import scala.annotation.tailrec
import scala.{specialized => sp}

trait Hash[Z] {
  def empty: Z

  def bytes(z: Z, bytes: ImmArray[Byte]): Z

  def byte(z: Z, x: Byte): Z =
    bytes(z, ImmArray(Array(x)))

  def short(z: Z, x: Short): Z =
    bytes(z, ImmArray(Array((x >>> 8).toByte, (x & 0xFF).toByte)))

  def int(z: Z, x: Int): Z =
    bytes(z, ImmArray(Array(
      (x >>> 24).toByte,
      ((x >>> 16) & 0xFF).toByte,
      ((x >>> 8) & 0xFF).toByte,
      (x & 0xFF).toByte)))

  def long(z: Z, x: Long): Z = bytes(z, ImmArray(Array(
    ((x >>> 56) & 0xFF).toByte,
    ((x >>> 48) & 0xFF).toByte,
    ((x >>> 40) & 0xFF).toByte,
    ((x >>> 32) & 0xFF).toByte,
    ((x >>> 24) & 0xFF).toByte,
    ((x >>> 16) & 0xFF).toByte,
    ((x >>> 8) & 0xFF).toByte,
    (x & 0xFF).toByte)))
}

final case class Murmur128(lowPart: Long, highPart: Long)
object Murmur128 {
  implicit val hash: Hash[Murmur128] = new Hash[Murmur128] {
    override def empty = Murmur128(0L, 0L)
    override def bytes(z: Murmur128, bytes: ImmArray[Byte]) = {
      val result = new Murmur3.LongPair()
      result.val1 = z.lowPart
      result.val2 = z.highPart
      Murmur3.murmurhash3_x64_128(bytes.unsafeValue, 0, bytes.length, result)
      Murmur128(result.val1, result.val2)
    }
  }
}

trait Eq[@sp -A] extends Any with Serializable {
  /**
    * Returns `true` if `x` and `y` are equal, `false` otherwise.
    */
  def eqv(first: A, second: A): Boolean

  /**
    * Returns `false` if `x` and `y` are equal, `true` otherwise.
    */
  def neqv(first: A, second: A): Boolean = !eqv(first, second)

  /**
    * Returns either a proof that the singleton values are equal or
    * a proof that the values are different.
    */
  def compare(x: A, y: A): Either[x.type =!= y.type, x.type === y.type] =
    if (eqv(x, y)) Right(Unsafe.is[x.type, y.type])
    else Left(Unsafe.weakApart[x.type, y.type])

  def hash[Z](value: A)(implicit Z: Hash[Z]): Z =
    hash1[Z](value, Z.empty)

  def hash1[Z](value: A, start: Z)(implicit hash: Hash[Z]): Z
}

// Bracket types:
// http://repository.cmu.edu/cgi/viewcontent.cgi?article=1073&context=philosophy
// https://www.youtube.com/watch?v=zQB1erzYxdI
// https://www.rocq.inria.fr/secret/Jean-Pierre.Tillich/publications/HashingSL2.pdf
// https://www.iacr.org/archive/crypto2000/18800288/18800288.pdf
// http://lib.dr.iastate.edu/cgi/viewcontent.cgi?article=15807&context=rtd

@SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
@SuppressWarnings(Array("org.wartremover.warts.Equals"))
object Eq {
  import java.lang.Double.doubleToRawLongBits
  import java.lang.Float.floatToRawIntBits

  def apply[A](implicit A: Eq[A]): Eq[A] = A

  def propositionEq[A]: Eq[A] = new Eq[A] {
    override def eqv(x: A, y: A): Boolean = true
    override def hash1[Z](value: A, start: Z)(implicit Z: Hash[Z]): Z = start
  }

  implicit val eqBool: Eq[Boolean] = new Eq[Boolean] {
    override def eqv(x: Boolean, y: Boolean): Boolean = x == y
    override def hash1[Z](value: Boolean, start: Z)(implicit Z: Hash[Z]): Z =
      Z.byte(start, if (value) 1.toByte else 0.toByte)
  }

  implicit val eqByte: Eq[Byte] = new Eq[Byte] {
    override def eqv(x: Byte, y: Byte): Boolean = x == y
    override def hash1[Z](value: Byte, start: Z)(implicit Z: Hash[Z]): Z = Z.byte(start, value)
  }

  implicit val eqShort: Eq[Short] = new Eq[Short] {
    override def eqv(x: Short, y: Short): Boolean = x == y
    override def hash1[Z](value: Short, start: Z)(implicit Z: Hash[Z]): Z = Z.short(start, value)
  }

  implicit val eqInt: Eq[Int] = new Eq[Int] {
    override def eqv(x: Int, y: Int): Boolean = x == y
    override def hash1[Z](value: Int, start: Z)(implicit Z: Hash[Z]): Z = Z.int(start, value)
  }

  implicit val eqLong: Eq[Long] = new Eq[Long] {
    override def eqv(x: Long, y: Long): Boolean = x == y
    override def hash1[Z](value: Long, start: Z)(implicit Z: Hash[Z]): Z = Z.long(start, value)
  }

  implicit val eqChar: Eq[Char] = new Eq[Char] {
    override def eqv(x: Char, y: Char): Boolean =
      x == y
    override def hash1[Z](value: Char, start: Z)(implicit Z: Hash[Z]): Z =
      Z.short(start, value.toShort)
  }

  implicit def eqArray[A](implicit A: Eq[A]): Eq[ImmArray[A]] = new Eq[ImmArray[A]] {
    override def eqv(x: ImmArray[A], y: ImmArray[A]): Boolean =
      x.unsafeValue sameElements y.unsafeValue

    override def hash1[Z](value: ImmArray[A], start: Z)(implicit Z: Hash[Z]): Z = {
      value.unsafeValue match {
        case b: Array[Byte] =>
          Z.bytes(start, ImmArray(b))

        case a: Array[_] =>
          @tailrec def go(v: Z, i: Int): Z =
            if (i < value.length) go(A.hash1(value.unsafeValue(i), v)(Z), i + 1)
            else v
          go(start, 0)
      }
    }
  }

  implicit val eqString: Eq[String] = new Eq[String] {
    override def eqv(x: String, y: String): Boolean =
      x == y
    override def hash1[Z](value: String, start: Z)(implicit Z: Hash[Z]): Z =
      Eq[ImmArray[Char]].hash1(ImmArray(value.toCharArray), start)(Z)
  }

  implicit val eqFloat:  Eq[Float] = new Eq[Float] {
    override def eqv(x: Float, y: Float): Boolean =
      floatToRawIntBits(x) == floatToRawIntBits(y)
    override def hash1[Z](value: Float, start: Z)(implicit Z: Hash[Z]): Z =
      Z.int(start, floatToRawIntBits(value))
  }

  implicit val eqDouble: Eq[Double] = new Eq[Double] {
    override def eqv(x: Double, y: Double): Boolean =
      doubleToRawLongBits(x) == doubleToRawLongBits(y)
    override def hash1[Z](value: Double, start: Z)(implicit Z: Hash[Z]): Z =
      Z.long(start, doubleToRawLongBits(value))
  }

  implicit val eqUnit: Eq[Unit] = new Eq[Unit] {
    override def eqv(x: Unit, y: Unit): Boolean = true
    override def hash1[Z](value: Unit, start: Z)(implicit Z: Hash[Z]): Z = start
  }

  implicit def option[T](implicit T: Eq[T]): Eq[Option[T]] = new Eq[Option[T]] {
    override def eqv(x: Option[T], y: Option[T]): Boolean =
      (x, y) match {
        case (None, None) => true
        case (Some(x), Some(y)) => T.eqv(x, y)
        case _ => false
      }

    override def hash1[Z](value: Option[T], start: Z)(implicit Z: Hash[Z]): Z =
      value match {
        case None => Z.byte(start, 0)
        case Some(x) => T.hash1(x, Z.byte(start, 0))
      }
  }

  implicit def pair[A, B](implicit A: Eq[A], B: Eq[B]): Eq[(A, B)] = new Eq[(A, B)] {
    override def eqv(x: (A, B), y: (A, B)): Boolean =
      (x, y) match {
        case ((x1, x2), (y1, y2)) => A.eqv(x1, y1) && B.eqv(x2, y2)
        case _ => false
      }

    override def hash1[Z](value: (A, B), start: Z)(implicit Z: Hash[Z]): Z =
      value match {
        case (x, y) => B.hash1(y, A.hash1(x, start))
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

    override def hash1[Z](value: Either[A, B], start: Z)(implicit Z: Hash[Z]): Z =
      value match {
        case Left(x) => A.hash1(x, Z.byte(start, 0))
        case Right(x) => B.hash1(x, Z.byte(start, 1))
      }
  }
}
