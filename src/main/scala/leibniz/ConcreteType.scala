package leibniz

sealed abstract class ConcreteType[A](val description: String) extends Product with Serializable

object ConcreteType {
  implicit def apply[A]: ConcreteType[A] =
    macro internal.MacroUtil.concreteType[A]

  def compare[A, B](A: ConcreteType[A], B: ConcreteType[B]): Either[Apart[A, B], A === B] =
    (A, B) match {
      case (CTNothing, CTNothing) => Right(Is.refl[Nothing])
      case (CTAny, CTAny) => Right(Is.refl[Any])
      // case (CTWiththat: CTIntersection[B] => this.parents.toSet == that.parents.toSet
//      case (CTSingleton(va, eqa, pa), CTSingleton(vb, eqb, pb)) =>
//        compare(pa, pb) match {
//          case Right(ab) => eqa.eqProof(va, vb) match {
//            case Some(p) => Right(p)
//            case None => Left()
//          }
//        }
//        (this.parent equal that.parent) &&
//          eq.eqv(this.value.asInstanceOf[A], that.value.asInstanceOf[A])
//      case b: CTRef[B] =>
//        name == b.name && params.sameElements(b.params)
    }

  final case object CTNothing extends ConcreteType[Nothing]("Nothing")
  final case object CTAny extends ConcreteType[Any]("Any")

  final case class CTWith[A](parents: Array[ConcreteType[_]])
    extends ConcreteType[A](parents.mkString(" with "))

  final case class CTSingleton[A, L <: A with Singleton]
  (value: L, eq: Eq[A], parent: ConcreteType[A])
    extends ConcreteType[L](s"$parent($value)")

  final case class CTRef[A](name: String, params: Array[ConcreteType[_]])
    extends ConcreteType[A](name + (if (params.isEmpty) "" else
      "[" + params.map(_.toString()).mkString(", ") + "]"))
}