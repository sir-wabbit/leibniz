package leibniz.internal

import scala.reflect.macros.{TypecheckException, blackbox}

final class ImplicationMacro(val c: blackbox.Context) {
  import c.universe._

  def mkImplies[A: c.WeakTypeTag, B: c.WeakTypeTag]: c.Tree = {
    val A = weakTypeOf[A]
    val B = weakTypeOf[B]

    val dummy0 = TermName(c.freshName)

    try c.typecheck(q"""
        {
          implicitly[_root_.leibniz.inhabitance.WeakProposition[$A]]
          implicitly[_root_.leibniz.inhabitance.WeakProposition[$B]]
          def run(implicit $dummy0: $A): $B = implicitly[$B]
          ((x: $A) => run(x)).asInstanceOf[_root_.leibniz.Implies.Type[$A, $B]]
        }
      """)
    catch {
      case TypecheckException(_, msg) =>
        c.abort(c.enclosingPosition, s"Could not prove that $A implies $B: $msg")
    }
  }
}