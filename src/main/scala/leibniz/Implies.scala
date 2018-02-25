package leibniz

import scala.reflect.macros.{TypecheckException, blackbox, whitebox}

trait Implies[A, B] {
  def apply(a: A): B
}
object Implies {
  def apply[A, B](implicit ev: Implies[A, B]): Implies[A, B] = ev

  implicit def mkImplies[A, B]: Implies[A, B] =
    macro ImplicationMacro.mkImplies[A, B]

  final class ImplicationMacro(val c: blackbox.Context) {
    import c.universe._

    def mkImplies[A: c.WeakTypeTag, B: c.WeakTypeTag]: c.Tree = {
      val A = weakTypeOf[A]
      val B = weakTypeOf[B]

      println(s"Implies[$A, $B]")

      val dummy0 = TermName(c.freshName)

      val tree = try {
        c.typecheck(
          q"""
          new Implies[$A, $B] {
            def run(implicit $dummy0: $A): $B = implicitly[$B]
            def apply($dummy0: $A): $B = run($dummy0)
          }
          """)
      } catch {
        case TypecheckException(_, _) =>
          c.abort(c.enclosingPosition, s"Could not prove that $A implies $B.")
      }
      tree
    }
  }
}