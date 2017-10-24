package leibniz

import org.scalatest.{FunSuite, Matchers}


class EqTest extends FunSuite with Matchers {
//  Eq[Boolean]
//  Eq[0]
//  Eq[Char]
//  Eq[Option[Either[Char, 0]]]
  Cosingleton[0]
  Cosingleton[Int]

  test("doubles") {
    val values: Array[Double] = Array(
      java.lang.Double.longBitsToDouble(0x7ff8000000000000L), // NaN
      java.lang.Double.longBitsToDouble(0x7ff8000000000001L), // NaN(1)
      java.lang.Double.longBitsToDouble(0xfff8000000000000L), // -NaN
      java.lang.Double.longBitsToDouble(0x7ff0000000000000L), // Infinity
      java.lang.Double.longBitsToDouble(0xfff0000000000000L), // -Infinity
      -0.0d, 0.0d,
      1.0d, -1.0d)

    val E = implicitly[Eq[Double]]

    val it = for {
      i <- values.indices
      j <- values.indices
    } yield (i == j && E.eqv(values(i), values(j))) || (i != j && E.neqv(values(i), values(j)))
    it.forall(x => x) should be (true)
  }

  test("floats") {
    val values: Array[Float] = Array(
      java.lang.Float.intBitsToFloat(0x7ff80000), // NaN
      java.lang.Float.intBitsToFloat(0x7ff80001), // NaN(1)
      java.lang.Float.intBitsToFloat(0xfff80000), // -NaN
      java.lang.Float.intBitsToFloat(0x7ff00000), // Infinity
      java.lang.Float.intBitsToFloat(0xfff00000), // -Infinity
      -0.0f, 0.0f,
      1.0f, -1.0f)

    val E = implicitly[Eq[Float]]

    val it = for {
      i <- values.indices
      j <- values.indices
    } yield (i == j && E.eqv(values(i), values(j))) || (i != j && E.neqv(values(i), values(j)))
    it.forall(x => x) should be (true)
  }

  final val boolFalse = false
  final val boolTrue = true

  final val byte0 = 0.toByte
  final val byte1 = 1.toByte
  final val byte255 = 255.toByte

  final val short0 = 0.toShort
  final val short1 = 1.toShort
  final val short65356 = (1 << 16 - 1).toShort

  final val floatNaN = java.lang.Float.intBitsToFloat(0x7ff80000)
  final val floatNaN1 = java.lang.Float.intBitsToFloat(0x7ff80001)
  final val floatMinusNaN = java.lang.Float.intBitsToFloat(0xfff80000)
  final val floatInfinity = java.lang.Float.intBitsToFloat(0x7ff00000)
  final val floatMinusInfinity = java.lang.Float.intBitsToFloat(0xfff00000)

  final val doubleNaN = java.lang.Double.longBitsToDouble(0x7ff80000)
  final val doubleNaN1 = java.lang.Double.longBitsToDouble(0x7ff80001)
  final val doubleMinusNaN = java.lang.Double.longBitsToDouble(0xfff80000)
  final val doubleInfinity = java.lang.Double.longBitsToDouble(0x7ff00000)
  final val doubleMinusInfinity = java.lang.Double.longBitsToDouble(0xfff00000)

  test("singletons") {
    val values: Array[Singleton] = Array(
      null,
      boolFalse, boolTrue,
      byte0, byte1, byte255,
      short0, short1, short65356,
      0, 1, -1,
      0L, 1L, -1L,
      -0.0f, 0.0f, 1.0f, -1.0f, floatNaN, floatNaN1, floatMinusNaN, floatInfinity, floatMinusInfinity,
      -0.0d, 0.0d, 1.0d, -1.0d, doubleNaN, doubleNaN1, doubleMinusNaN, doubleInfinity, doubleMinusInfinity,
      "ABC",
      "abc",
      "",
      'a, 'b,
      'a', 'b',
      None)

    val E = Eq.singletonEq[Singleton]

    val it = for {
      i <- values.indices
      j <- values.indices
    } yield (i == j && E.eqv(values(i), values(j))) || (i != j && E.neqv(values(i), values(j)))
    it.forall(x => x) should be (true)
  }
}
