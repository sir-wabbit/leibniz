package leibniz

import macrocompat.bundle
import scala.reflect.macros.blackbox

sealed abstract class ConcreteType[A] {
  def compare[B](b: ConcreteType[B]): Either[A =!= B, A === B]
}

object ConcreteType {
  implicit def apply[A]: ConcreteType[A] =
    macro MacroUtil.concreteType[A]

  final case object CTNothing extends ConcreteType[Nothing] {
    def compare[B](b: ConcreteType[B]): Either[Nothing =!= B, Nothing === B] = b match {
      case CTNothing => Right(Is.unsafeForce[Nothing, B])
      case _ => Left(Apart.Forced[Nothing, B](this, b))
    }
    override def toString: String = "Nothing"
  }

  final case object CTAny extends ConcreteType[Any] {
    def compare[B](b: ConcreteType[B]): Either[Any =!= B, Any === B] = b match {
      case CTAny => Right(Is.unsafeForce[Any, B])
      case _ => Left(Apart.Forced[Any, B](this, b))
    }
    override def toString: String = "Any"
  }

  final case class CTSingleton[A](A: A)(name: String) extends ConcreteType[A] {
    def compare[B](b: ConcreteType[B]): Either[A =!= B, A === B] = b match {
      case CTSingleton(A) => Right(Is.unsafeForce[A, B])
      case _ => Left(Apart.Forced[A, B](this, b))
    }
    override def toString: String = s"$name($A)"
  }

  final case class CTRef[A](Name: String, Params: List[ConcreteType[_]]) extends ConcreteType[A] {
    def compare[B](b: ConcreteType[B]): Either[A =!= B, A === B] = b match {
      case CTRef(Name, Params) => Right(Is.unsafeForce[A, B])
      case _ => Left(Apart.Forced[A, B](this, b))
    }
    override def toString: String =
      Name + (if (Params.isEmpty) "" else
        "[" + Params.map(_.toString()).mkString(", ") + "]")
  }
}

final class MacroUtil(val c: blackbox.Context) {
  import c.universe._
  import internal._
  import definitions.NothingClass

  val typeableTpe = typeOf[ConcreteType[_]].typeConstructor
  val nothingType = NothingClass.toType
  val anyType = typeOf[Any]

  def isConcreteType(tpe: Type): Boolean = {
    val dealiased = tpe.dealias

    dealiased match {
      case t if (t <:< nothingType) && (nothingType <:< t) =>
        true
      case t if (t <:< anyType) && (anyType <:< t) =>
        true

      case SingleType(_, v) if !v.isParameter =>
        val name = v.name.toString
        true

      case ConstantType(c) =>
        val name = c.tpe.typeSymbol.name.toString
        true

      case t: TypeRef =>
        val args = t.typeArgs.map(makeConcreteType)
        true

      case _ =>
        false
    }
  }

  def makeConcreteType(tpe: Type): c.Tree = {
    val dealiased = tpe.dealias

    dealiased match {
      case t if (t <:< nothingType) && (nothingType <:< t) =>
        q"""_root_.leibniz.ConcreteType.CTNothing"""
      case t if (t <:< anyType) && (anyType <:< t) =>
        q"""_root_.leibniz.ConcreteType.CTAny"""

      case SingleType(_, v) if !v.isParameter =>
        val name = v.name.toString
        q"""_root_.leibniz.ConcreteType.CTSingleton[$tpe]($v.asInstanceOf[$tpe])($name)"""

      case ConstantType(c) =>
        val name = c.tpe.typeSymbol.name.toString
        q"""_root_.leibniz.ConcreteType.CTSingleton[$tpe]($c.asInstanceOf[$tpe])($name)"""

      case t: TypeRef =>
        val args = t.typeArgs.map(makeConcreteType)
        q"""_root_.leibniz.ConcreteType.CTRef[$tpe](${t.sym.fullName}, List(..$args))"""

      case _ =>
        c.abort(c.enclosingPosition, s"Could not make a concrete type for $tpe.")
    }
  }

  def concreteType[A : c.WeakTypeTag]: c.Tree = {
    val tpe = weakTypeOf[A]
    makeConcreteType(tpe)
  }

  def apart[A : c.WeakTypeTag, B : c.WeakTypeTag]: c.Tree = {
    val ta = weakTypeOf[A]
    val tb = weakTypeOf[B]
    if (isConcreteType(ta) && isConcreteType(tb) && !(ta =:= tb)) {
      val ca = makeConcreteType(ta)
      val cb = makeConcreteType(tb)
      q"""_root_.leibniz.Apart.unsafeForce[$ta, $tb]($ca, $cb)"""
    } else {
      c.abort(c.enclosingPosition, s"Could not prove that $ta =!= $tb.")
    }
  }
}