package leibniz.macros

import scala.reflect.macros.blackbox

import scala.annotation.StaticAnnotation

class newtype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro NewTypeMacros.newtypeAnnotation
}

private[macros] object NewTypeMacros {

  def newtypeAnnotation(c: blackbox.Context)(annottees: c.Tree*): c.Tree = {

    import c.universe._

    def fail(msg: String) = c.abort(c.enclosingPosition, msg)

    def run() = annottees match {
      case List(clsDef: ClassDef) => runClass(clsDef)
      case List(clsDef: ClassDef, modDef: ModuleDef) => runClassWithObj(clsDef, modDef)
      case _ => fail("Unsupported newtype definition")
    }

    def runClass(clsDef: ClassDef) = {
      runClassWithObj(clsDef, q"object ${clsDef.name.toTermName}".asInstanceOf[ModuleDef])
    }

    def runClassWithObj(clsDef: ClassDef, modDef: ModuleDef) = {

      val ClassDef(mods, typeName, tparams, template) = clsDef
      val Template(parents, _, body) = template

      val q"object $objName extends { ..$objEarlyDefs } with ..$objParents { $objSelf => ..$objDefs }" = modDef

      val ctor = getConstructor(body)
      val valDef = extractConstructorValDef(ctor)
      val shouldGenerateApplyMethod = mods.hasFlag(Flag.CASE)

      val shouldGenerateValExtensionMethod = body.collectFirst {
        case vd: ValDef if vd.mods.hasFlag(Flag.PARAMACCESSOR) && vd.name == valDef.name => ()
      }.isDefined

      val instanceMethods = getInstanceMethods(body)

      validateParents(parents)

      val baseRefinementName = TypeName(typeName.decodedName + "$newtype")

      if (tparams.isEmpty) {

        val maybeApplyMethod = if (!shouldGenerateApplyMethod) Nil else List(
          q"def apply(${valDef.name}: ${valDef.tpt}): Type = ${valDef.name}.asInstanceOf[Type]"
        )

        val maybeValDefMethod = if (!shouldGenerateValExtensionMethod) Nil else List(
          q"def ${valDef.name}: ${valDef.tpt} = repr.asInstanceOf[${valDef.tpt}]"
        )

        val extensionMethods = maybeValDefMethod ++ instanceMethods

        val maybeOpsDef = if (extensionMethods.isEmpty) Nil else List(
          q"""
            implicit final class Ops$$newtype(private val repr: Type) extends AnyVal {
              ..$extensionMethods
            }
          """
        )
//
//        val coercibleInstances = List(
//          q"@inline implicit def unsafeWrap: $CoercibleCls[Repr, Type] = $CoercibleObj.instance",
//          q"@inline implicit def unsafeUnwrap: $CoercibleCls[Type, Repr] = $CoercibleObj.instance",
//          q"@inline implicit def unsafeWrapM[M[_]]: $CoercibleCls[M[Repr], M[Type]] = $CoercibleObj.instance",
//          q"@inline implicit def unsafeUnwrapM[M[_]]: $CoercibleCls[M[Type], M[Repr]] = $CoercibleObj.instance",
//          // Avoid ClassCastException with Array types by prohibiting Array coercing.
//          q"@inline implicit def cannotWrapArrayAmbiguous1: $CoercibleCls[Array[Repr], Array[Type]] = $CoercibleObj.instance",
//          q"@inline implicit def cannotWrapArrayAmbiguous2: $CoercibleCls[Array[Repr], Array[Type]] = $CoercibleObj.instance",
//          q"@inline implicit def cannotUnwrapArrayAmbiguous1: $CoercibleCls[Array[Type], Array[Repr]] = $CoercibleObj.instance",
//          q"@inline implicit def cannotUnwrapArrayAmbiguous2: $CoercibleCls[Array[Type], Array[Repr]] = $CoercibleObj.instance"
//        )

        q"""
          type $typeName = ${typeName.toTermName}.Type
          object $objName extends { ..$objEarlyDefs } with ..$objParents { $objSelf =>
            ..$objDefs
            type Repr = ${valDef.tpt}
            type Base = { type $baseRefinementName }
            trait Tag
            type Type = Base with Tag
            ..$maybeApplyMethod
            ..$maybeOpsDef
          }
        """

      } else {
        // NewTypes with arity

        // Converts [F[_], A] to [F, A]; needed for applying the defined type params.
        val tparamNames: List[TypeName] = tparams.map(_.name)

        // Type params with variance removed for building methods.
        val tparamsNoVar: List[TypeDef] = tparams.map(td =>
          TypeDef(Modifiers(Flag.PARAM), td.name, td.tparams, td.rhs)
        )

        val maybeApplyMethod = if (!shouldGenerateApplyMethod) Nil else List(
          q"def apply[..$tparamsNoVar](${valDef.name}: ${valDef.tpt}): Type[..$tparamNames] = ${valDef.name}.asInstanceOf[Type[..$tparamNames]]"
        )

        val maybeValDefMethod = if (!shouldGenerateValExtensionMethod) Nil else List(
          q"def ${valDef.name}: ${valDef.tpt} = repr.asInstanceOf[${valDef.tpt}]"
        )

        val extensionMethods = maybeValDefMethod ++ instanceMethods

        val maybeOpsDef = if (extensionMethods.isEmpty) Nil else List(
          q"""
            implicit final class Ops$$newtype[..$tparams](private val repr: Type[..$tparamNames]) extends AnyVal {
              ..$extensionMethods
            }
          """
        )
//
//        val coercibleInstances = List[Tree](
//          q"@inline implicit def unsafeWrap[..$tparamsNoVar]: $CoercibleCls[Repr[..$tparamNames], Type[..$tparamNames]] = $CoercibleObj.instance",
//          q"@inline implicit def unsafeUnwrap[..$tparamsNoVar]: $CoercibleCls[Type[..$tparamNames], Repr[..$tparamNames]] = $CoercibleObj.instance",
//          q"@inline implicit def unsafeWrapM[M[_], ..$tparamsNoVar]: $CoercibleCls[M[Repr[..$tparamNames]], M[Type[..$tparamNames]]] = $CoercibleObj.instance",
//          q"@inline implicit def unsafeUnwrapM[M[_], ..$tparamsNoVar]: $CoercibleCls[M[Type[..$tparamNames]], M[Repr[..$tparamNames]]] = $CoercibleObj.instance",
//          // Avoid ClassCastException with Array types by prohibiting Array coercing.
//          q"@inline implicit def cannotWrapArrayAmbiguous1[..$tparamsNoVar]: $CoercibleCls[Array[Repr[..$tparamNames]], Array[Type[..$tparamNames]]] = $CoercibleObj.instance",
//          q"@inline implicit def cannotWrapArrayAmbiguous2[..$tparamsNoVar]: $CoercibleCls[Array[Repr[..$tparamNames]], Array[Type[..$tparamNames]]] = $CoercibleObj.instance",
//          q"@inline implicit def cannotUnwrapArrayAmbiguous1[..$tparamsNoVar]: $CoercibleCls[Array[Type[..$tparamNames]], Array[Repr[..$tparamNames]]] = $CoercibleObj.instance",
//          q"@inline implicit def cannotUnwrapArrayAmbiguous2[..$tparamsNoVar]: $CoercibleCls[Array[Type[..$tparamNames]], Array[Repr[..$tparamNames]]] = $CoercibleObj.instance"
//        )

        q"""
          type $typeName[..$tparams] = ${typeName.toTermName}.Type[..$tparamNames]
          object $objName extends { ..$objEarlyDefs } with ..$objParents { $objSelf =>
            ..$objDefs
            type Repr[..$tparams] = ${valDef.tpt}
            type Base = { type $baseRefinementName }
            trait Tag[..$tparams]
            type Type[..$tparams] = Base with Tag[..$tparamNames]
            ..$maybeApplyMethod
            ..$maybeOpsDef
          }
        """
      }
    }

    def getConstructor(body: List[Tree]): DefDef = body.collectFirst {
      case dd: DefDef if dd.name == termNames.CONSTRUCTOR => dd
    }.getOrElse(fail("Failed to locate constructor"))

    def getInstanceMethods(body: List[Tree]): List[DefDef] = body.flatMap {
      case vd: ValDef =>
        if (vd.mods.hasFlag(Flag.CASEACCESSOR) || vd.mods.hasFlag(Flag.PARAMACCESSOR)) Nil
        else fail("val definitions not supported, use def instead")
      case dd: DefDef =>
        if (dd.name == termNames.CONSTRUCTOR) Nil else List(dd)
      case x =>
        fail(s"illegal definition in newtype: $x")
    }

    def extractConstructorValDef(dd: DefDef): ValDef = dd.vparamss match {
      case List(List(vd)) => vd
      case _ => fail("Unsupported constructor, must have exactly one argument")
    }

    def validateParents(parents: List[Tree]): Unit = {
      val ignoredExtends = List(tq"scala.Product", tq"scala.Serializable", tq"scala.AnyRef")
      val unsupported = parents.filterNot(t => ignoredExtends.exists(t.equalsStructure))
      if (unsupported.nonEmpty) {
        fail(s"newtypes do not support inheritance; illegal supertypes: ${unsupported.mkString(", ")}")
      }
    }

    run()
  }
}
