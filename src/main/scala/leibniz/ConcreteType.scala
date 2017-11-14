package leibniz

sealed abstract class ConcreteType[A] extends Product with Serializable

object ConcreteType {
  implicit def apply[A]: ConcreteType[A] =
    macro internal.MacroUtil.concreteType[A]

  type Type[A] = ConcreteType[A]

  def compare[A, B](A: Type[A], B: Type[B]): Either[Apart[A, B], A === B] = {
    import leibniz.internal.Unsafe.unsafe
    if (A == B) Right(Is.force[A, B])
    else Left(Apart.force[A, B](A, B))
  }

  final case class CTSingleton[A, L <: A with Singleton]
  (parent: Type[A], value: L, eq: Eq[A]) extends Type[L] {
    override def equals(other: Any): Boolean = other match {
      case that: CTSingleton[a, l] =>
        this.parent == that.parent &&
          this.eq.eqv(this.value, that.value.asInstanceOf[A])
      case _ => false
    }
  }

  final case class CTNominal[A](name: String, args: List[Type[_]]) extends Type[A] {
    override def equals(other: Any): Boolean = other match {
      case that: CTNominal[b] =>
          this.name == that.name &&
          this.args == that.args
      case _ => false
    }
  }
}