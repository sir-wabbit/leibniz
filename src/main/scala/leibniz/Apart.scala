package leibniz

import macrocompat.bundle
import scala.reflect.macros.blackbox

sealed abstract class Typeable[A] {
  def cmp[B](b: Typeable[B]): Either[A =!= B, A === B]
  def describe: String
}

object Typeable {
  implicit def apply[A]: Typeable[A] =
    macro Macro.impl[A]

  final case object NothingTypeable extends Typeable[Nothing] {
    def cmp[B](b: Typeable[B]): Either[Nothing =!= B, Nothing === B] = b match {
      case NothingTypeable => Right(Is.unsafeForce[Nothing, B])
      case _ => Left(Apart.Forced[Nothing, B](this, b))
    }
    def describe: String = "Nothing"
  }

  final class Macro(val c: blackbox.Context) {
    import c.universe._
    import internal._
    import definitions.NothingClass

    val typeableTpe = typeOf[Typeable[_]].typeConstructor

    def impl[A : c.WeakTypeTag]: c.Tree = {
      val tpe = weakTypeOf[A]
      val dealiased = tpe.dealias

      dealiased match {
        case t: TypeRef if t.sym == NothingClass =>
          q"""_root_.leibniz.Typeable.NothingTypeable"""
        case t if (t <:< NothingClass.toType) && (NothingClass.toType <:< t) =>
          q"""_root_.leibniz.Typeable.NothingTypeable"""

        case _ =>
          c.abort(c.enclosingPosition, "Could not find a Typeable.")
      }
    }
  }
}

sealed abstract class Apart[A, B] { nab =>
  def proof[F[_]](f: F[A] === F[B]): Constant[F]

  def choose[C](C: Typeable[C]): Either[A =!= C, B =!= C]

  def flip: B =!= A = new (B =!= A) {
    def proof[F[_]](f: F[B] === F[A]): Constant[F] =
      nab.proof[F](f.flip)

    def choose[C](C: Typeable[C]): Either[B =!= C, A =!= C] =
      nab.choose[C](C).swap

    override def flip: A =!= B = nab
  }

  def contradicts[R](ab: A === B): R = {
    type f[x] = x
    nab.proof[f](ab).proof[Unit, R].subst[f](())
  }
}
object Apart {
  def irreflexive[A](ev: A =!= A): Void =
    ev.contradicts(Is.refl[A])

  private[leibniz] final case class Forced[A, B](A: Typeable[A], B: Typeable[B]) extends Apart[A, B] {
    def proof[F[_]](f: F[A] === F[B]): Constant[F] = new Constant[F] {
      def proof[X, Y]: F[X] === F[Y] = Is.unsafeForce[F[X], F[Y]]
    }

    def choose[C](C: Typeable[C]): Either[A =!= C, B =!= C] =
      A.cmp(C) match {
        case Right(_) => B.cmp(C) match {
          case Right(_) => ???
          case Left(p) => Right(p)
        }
        case Left(p) => Left(p)
      }
  }
}