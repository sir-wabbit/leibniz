package leibniz.internal

import leibniz.{ConcreteType, Eq}

import scala.reflect.macros.blackbox
import scala.reflect.macros.whitebox

sealed abstract class Shared[C <: blackbox.Context] {
  val c: C
  import c.universe._
  import definitions.{ NothingClass, AnyClass }

  final val NothingType: Type = NothingClass.toType
  final val AnyType: Type = AnyClass.toType

  final val EqType: Symbol = typeOf[Eq[_]].typeSymbol
  final val EqTypeConstructor: Type = typeOf[Eq[_]].typeConstructor

  def findCosingleton(tpe: Type): Option[(c.Tree, c.Type)] = {
    val exactEq = c.inferImplicitValue(appliedType(EqTypeConstructor, tpe), silent = true)

    if (exactEq != EmptyTree) {
      exactEq.tpe match {
        case TypeRef(_, EqType, List(result)) => Some((exactEq, result))
        case _ => None
      }
    } else {
      println(tpe)
      None
    }
  }
}

final class Whitebox(val c: whitebox.Context) extends Shared[whitebox.Context] {
  import c.universe._
  import internal._
  import definitions.NothingClass

  def cosingleton[A : c.WeakTypeTag]: c.Tree = {
    val tpe = weakTypeOf[A]
    findCosingleton(tpe) match {
      case Some((_, x)) =>
        q"""new _root_.leibniz.Cosingleton[$tpe] { type Result = $x } """
      case None =>
        c.abort(c.enclosingPosition, s"Could not find a cosingleton for $tpe.")
    }
  }
}

final class MacroUtil(val c: blackbox.Context) extends Shared[blackbox.Context] {
  import c.universe._
  import internal._


  val typeableTpe = typeOf[ConcreteType[_]].typeConstructor

  def isConcreteType(tpe: Type): Boolean = {
    val dealiased = tpe.dealias

    dealiased match {
      case t if (t <:< NothingType) && (NothingType <:< t) =>
        true

      case t if (t <:< AnyType) && (AnyType <:< t) =>
        true

      case SingleType(_, v) if !v.isParameter =>
        val name = v.name.toString
        true

      case ConstantType(c) =>
        val name = c.tpe.typeSymbol.name.toString
        true

      case t: TypeRef if t.typeSymbol.isClass =>
        t.typeArgs.forall(isConcreteType)

      case _ =>
        false
    }
  }

  def makeConcreteType(tpe: Type): c.Tree = {
    val dealiased = tpe.dealias

//    c.warning(c.enclosingPosition,
//      dealiased.toString + "\n" +
//        tpe.toString + "\n" +
//        tpe.getClass.toString)

    dealiased match {
      case t if (t <:< NothingType) && (NothingType <:< t) =>
        // Nothing
        q"""_root_.leibniz.ConcreteType.CTNothing"""

      case t if (t <:< AnyType) && (AnyType <:< t) =>
        // Any.
        q"""_root_.leibniz.ConcreteType.CTAny"""

      case SingleType(prefix, path) if !path.isParameter =>
        // p # t
//        println(prefix)
//        println(path)

        val name = path.name.toString

        findCosingleton(tpe) match {
          case Some((eq, cosingleton)) =>
            val parent = makeConcreteType(cosingleton)
            q"""new _root_.leibniz.ConcreteType.CTSingleton[$cosingleton, $tpe]($name, $path.asInstanceOf[$tpe], $eq, $parent)"""
          case None =>
            c.abort(c.enclosingPosition, s"Could not make a concrete type for $tpe: no Eq[$tpe] found.")
        }

      case ConstantType(value) =>
        // 0, "a", etc
        val name = value.tpe.typeSymbol.name.toString

        findCosingleton(tpe) match {
          case Some((eq, cosingleton)) =>
            val parent = makeConcreteType(cosingleton)
            q"""new _root_.leibniz.ConcreteType.CTSingleton[$cosingleton, $tpe]($name, $value.asInstanceOf[$tpe], $eq, $parent)"""
          case None =>
            c.abort(c.enclosingPosition, s"Could not make a concrete type for $tpe: no Eq[$tpe] found.")
        }

      case RefinedType(parents, decls) =>
        // a with b { }
        if(decls.nonEmpty)
          c.abort(c.enclosingPosition, "Refinements with non-empty scope are not yet supported.")

        val parentTypes = parents.filterNot(_ =:= typeOf[AnyRef]).map { parent =>
          c.inferImplicitValue(appliedType(typeableTpe, List(parent)))
        }

        if (parentTypes.contains(EmptyTree))
          c.abort(c.enclosingPosition, "Missing ConcreteType for parent of a refinement")

        if (parentTypes.length != 1)
          q"""
            new _root_.leibniz.ConcreteType.CTIntersection(
              _root_.scala.Array[_root_.leibniz.ConcreteType[_]](..$parentTypes)
            )
           """
        else
          parentTypes.head

      case t: TypeRef if t.typeSymbol.isClass =>
        // Class[..]
        val args = t.typeArgs.map(makeConcreteType)
        q"""
          new _root_.leibniz.ConcreteType.CTRef[$tpe](${t.sym.fullName},
            _root_.scala.Array[_root_.leibniz.ConcreteType[_]](..$args))
        """

      case _ =>
        c.abort(c.enclosingPosition, s"Could not make a concrete type for $tpe: unrecognized type.")
    }
  }

  def concreteType[A : c.WeakTypeTag]: c.Tree = {
    val tpe = weakTypeOf[A]
    makeConcreteType(tpe)
  }

  def apart[A : c.WeakTypeTag, B : c.WeakTypeTag]: c.Tree = {
    val ta = weakTypeOf[A]
    val tb = weakTypeOf[B]
    if (isConcreteType(ta) && isConcreteType(tb) && !(ta <:< tb && tb <:< ta)) {
      val ca = makeConcreteType(ta)
      val cb = makeConcreteType(tb)
      q"""_root_.leibniz.Apart.unsafeForce[$ta, $tb]($ca, $cb)"""
    } else {
      c.abort(c.enclosingPosition, s"Could not prove that $ta =!= $tb.")
    }
  }
}