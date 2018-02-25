package leibniz

import scala.reflect.macros.{TypecheckException, blackbox}
import scala.util.control.NonFatal

trait Forall2[R[_, _]] {
  def apply[A, B]: R[A, B]
}

trait Forall[F[_]] {
  def apply[A]: F[A]
}
trait ForallLowerPriority {
  import Forall._

  implicit def mkForall0[A](implicit ev: A): Forall[λ[x => A]] =
    new Forall[λ[x => A]] {
      def apply[X]: A = ev
    }
}
object Forall extends ForallLowerPriority {
  def apply[F[_]](implicit ev: Forall[F]): Forall[F] = ev

  implicit def mkForall[F[_]]: Forall[F] =
    macro ForallMacro.mkForall[F]

  sealed trait Hidden$1 extends Any
  final class MkForall$1[F[_]](val fh: F[Hidden$1]) extends Forall[F] {
    def apply[A]: F[A] = fh.asInstanceOf[F[A]]
  }

  final class ForallMacro(val c: blackbox.Context) {
    import c.universe._

    val hidden = typeOf[Hidden$1]

    def mkForall[F[_]](implicit f: c.WeakTypeTag[F[_]]): c.Tree = {
      val F = weakTypeOf[F[_]]

      println(s"Forall[$F]")

      val T = appliedType(F.typeConstructor, hidden)

      val tree = try {
        c.typecheck(
          q"""
          new _root_.leibniz.Forall.MkForall$$1[${F.typeConstructor}](implicitly[$T])
          """)
      } catch {
        case TypecheckException(_, msg) =>
          println("ERROR")
          c.abort(c.enclosingPosition, s"Could not prove $F for all arguments: $msg")
      }
      tree
    }
  }
}
