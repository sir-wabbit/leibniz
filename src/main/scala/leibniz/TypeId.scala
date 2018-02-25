package leibniz

import leibniz.internal.Unsafe

import scala.annotation.tailrec

final case class TypeId[A] private (lowPart: Long, highPart: Long) { A =>
  def compare[B](B: TypeId[B]): Either[Apart[A, B], A === B] =
    TypeId.compare[A, B](A, B)
}
object TypeId {
  implicit def apply[A]: TypeId[A] =
    macro internal.MacroUtil.mkTypeId[A]

  def compare[A, B](A: TypeId[A], B: TypeId[B]): Either[Apart[A, B], A === B] =
    if (A == B) Right(Unsafe.is[A, B]) else Left(Apart.witness(Unsafe.weakApart[A, B], A, B))

  def $create[A](lowPart: Long, highPart: Long): TypeId[A] =
    TypeId(lowPart, highPart)

  def $nominal[A](name: String, args: Array[TypeId[_]]): TypeId[A] = {
    @tailrec def go(z: Murmur128, i: Int): Murmur128 =
      if (i < args.length) {
        val z1 = Eq[Long].hash1[Murmur128](args(i).highPart, z)
        val z2 = Eq[Long].hash1[Murmur128](args(i).lowPart, z1)
        go(z2, i + 1)
      } else z

    val z = go(Eq[String].hash[Murmur128](name), 0)
    TypeId(z.lowPart, z.highPart)
  }

  def $singleton[P, A <: P with Singleton](parent: TypeId[P], value: A, P: Eq[P]): TypeId[A] = {
    val z1 = Eq[Long].hash[Murmur128](parent.highPart)
    val z2 = Eq[Long].hash1[Murmur128](parent.lowPart, z1)
    val z3 = P.hash1[Murmur128](value, z2)
    TypeId(z3.lowPart, z3.highPart)
  }
}