package leibniz

import leibniz.inhabitance.Proposition

import scala.reflect.macros.{TypecheckException, blackbox}
import scala.util.control.NonFatal

object Forall {
  type Base
  trait Tag extends Any
  type Type[F[_]]    <: Base with Tag

  def apply[F[_]](implicit ev: Type[F]): Type[F] = ev

  sealed trait $Hidden extends Any

  implicit def mkForall[F[_]]: Type[F] = macro ForallMacro.mkForall[F]
  final class ForallMacro(val c: blackbox.Context) {
    import c.universe._
    def mkForall[F[_]](implicit f: c.WeakTypeTag[F[_]]): c.Tree = {
      val F = weakTypeOf[F[_]]
      val T = appliedType(F.typeConstructor, typeOf[$Hidden])
      try c.typecheck(q"implicitly[$T].asInstanceOf[_root_.leibniz.Forall.Type[$F]]")
      catch {
        case TypecheckException(_, msg) =>
          c.abort(c.enclosingPosition, s"Could not prove $F for all arguments: $msg")
      }
    }
  }

  implicit final class $MkForall(val t: Forall.type) extends AnyVal {
    type Hidden

    def witness[F[_]](fa: F[Hidden]): Type[F] =
      fa.asInstanceOf[Type[F]]

    def witnessT[F[_]](ft: TypeHolder[Hidden] => F[Hidden]): Type[F] =
      witness(ft(TypeHolder[Hidden]))
  }

  implicit final class ForallOps[F[_]](val fx: Type[F]) extends AnyVal {
    def apply[A]: F[A] = fx.asInstanceOf[F[A]]

    def toFunctionK[G[_], H[_]](implicit p: F =~= λ[x => G[x] => H[x]]): G ~> H =
      FunctionK.witnessT[G, H] { t =>
        p.apply(fx.apply[t.Type])
      }
  }

  implicit def proposition[F[_]](implicit ev: Forall[λ[x => Proposition[F[x]]]]): Proposition[Forall[F]] =
    (A: ¬¬[Forall[F]]) => Forall.witnessT { t =>
      val p: ¬¬[F[t.Type]] = A.map(_.apply[t.Type])
      ev.apply[t.Type].proved(p)
    }
}
