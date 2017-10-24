package leibniz

sealed abstract class ConcreteType[A] extends Product with Serializable {
  def compare[B](b: ConcreteType[B]): Either[Apart[A, B], A === B] = {
    import Unsafe._
    if (equal(b)) Right(Is.force[A, B])
    else Left(Apart.force[A, B](this, b))
  }

  def equal[B](b: ConcreteType[B]): Boolean

  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  override def equals(obj: scala.Any): Boolean =
    if (obj == null) false
    else if (obj.getClass != this.getClass) false
    else equal(obj.asInstanceOf[ConcreteType[_]])
}

object ConcreteType {
  implicit def apply[A]: ConcreteType[A] =
    macro internal.MacroUtil.concreteType[A]

  final case object CTNothing extends ConcreteType[Nothing] {
    def equal[B](b: ConcreteType[B]): Boolean =
      b.isInstanceOf[CTNothing.type]
    override def toString: String = "Nothing"
  }

  final case object CTAny extends ConcreteType[Any] {
    def equal[B](b: ConcreteType[B]): Boolean =
      b.isInstanceOf[CTAny.type]
    override def toString: String = "Any"
  }

  final case class CTIntersection[A](parents: Array[ConcreteType[_]]) extends ConcreteType[A] {
    def equal[B](b: ConcreteType[B]): Boolean = b match {
      case that: CTIntersection[B] => this.parents.toSet == that.parents.toSet
      case _ => false
    }
    override def toString: String = parents.mkString(" with ")
  }

  final case class CTSingleton[A, L <: A with Singleton]
  (name: String, value: L, eq: Eq[A], parent: ConcreteType[A]) extends ConcreteType[L] {
    def equal[B](b: ConcreteType[B]): Boolean = b match {
      case that: CTSingleton[a, l] =>
        (this.parent equal that.parent) &&
          eq.eqv(this.value.asInstanceOf[A], that.value.asInstanceOf[A])
      case _ => false
    }
    override def toString: String = s"$name($value)"
  }

  final case class CTRef[A](name: String, params: Array[ConcreteType[_]]) extends ConcreteType[A] {
    def equal[B](b: ConcreteType[B]): Boolean = b match {
      case b: CTRef[B] =>
        name == b.name && params.sameElements(b.params)
      case _ => false
    }

    override def toString: String =
      name + (if (params.isEmpty) "" else
        "[" + params.map(_.toString()).mkString(", ") + "]")
  }
}