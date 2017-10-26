import cats.Id
import leibniz._
import leibniz.inhabitance.{Inhabited, Proposition, SingletonOf, Uninhabited}
import org.scalatest.FunSpec

import scala.annotation.unchecked.uncheckedVariance

@SuppressWarnings(Array(
  "org.wartremover.warts.NonUnitStatements",
  "org.wartremover.warts.Nothing",
  "org.wartremover.warts.Any"))
class Resolution extends FunSpec {
  implicitly[Int <~< Int]
  implicitly[Int <~< AnyVal]

  implicitly[String <~< String]
  implicitly[String <~< AnyRef]
  implicitly[String <~< Any]

  implicitly[Nothing <~< Int]
  implicitly[Nothing <~< String]
  implicitly[Nothing <~< AnyRef]
  implicitly[Nothing <~< AnyVal]
  implicitly[Nothing <~< Any]

  implicitly[Null <~< String]
  implicitly[Null <~< AnyRef]
  implicitly[Null <~< Any]

  implicitly[Int === Int]
  implicitly[Nothing === Nothing]
  implicitly[Any === Any]

  implicitly[List =~= List]
  implicitly[Id =~= Id]
  implicitly[Either[Int, ?] =~= Either[Int, ?]]
  implicitly[(Int => ?) =~= (Int => ?)]
  // implicitly[(? => Int) =~= (? => Int)]

//  trait Nat[X <: Nat[X]]
//  final case class Z() extends Nat[Z]
//  final case class S[N](n: N) extends Nat[S[N]]
//  implicitly[IsF[Nat, Z, Z]]

  implicitly[(String, Int) <~< (String, Any)]
  implicitly[(String, Int) <~< (Any, Any)]
  implicitly[(String, Int) <~< (AnyRef, AnyVal)]
  implicitly[(String, Int) <~< AnyRef]
  implicitly[(String, Int) <~< Any]
  implicitly[Null <~< (String, Int)]
  implicitly[Nothing <~< (String, Int)]

  trait A { type X }
  def f1(a: A): a.X === a.X = implicitly[Is[a.X, a.X]]
  def f2(a: A): a.X <~< a.X = implicitly[As[a.X, a.X]]
  def f3(a: A): As1[a.X, a.X] = implicitly[As1[a.X, a.X]]

  implicitly[Int As1 AnyVal]

  trait F[L, H >: L] { type A >: L <: (H with B); type B >: L <: H }
  def g1[L, H >: L](a: F[L, H]): Is[a.A, a.A] = implicitly[Is[a.A, a.A]]
  def g2[L, H >: L](a: F[L, H]): As[a.A, a.B] = implicitly[As[a.A, a.B]]
  def g3[L, H >: L](a: F[L, H]): As[a.A, a.B] = implicitly[As[a.A, a.B]]

  def h1[A, B >: A]: As[A, B] = implicitly[As[A, B]]
  def h2[A]: Is[A, A] = implicitly[Is[A, A]]
  def h3[A]: As[A, A] = implicitly[As[A, A]]

  implicitly[Bounded[Nothing, AnyVal, Int]]
  implicitly[Bounded[Int, AnyVal, Int]]
  implicitly[Bounded[Nothing, Int, Int]]
  implicitly[Bounded[Int, Int, Int]]

  implicitly[Liskov[Nothing, Any, Int, AnyVal]]
  implicitly[Liskov[Int, Any, Int, AnyVal]]
  implicitly[Liskov[Int, AnyVal, Int, AnyVal]]

  implicitly[Liskov1[Nothing, Any, Int, AnyVal]]
  implicitly[Liskov1[Int, Any, Int, AnyVal]]
  implicitly[Liskov1[Int, AnyVal, Int, AnyVal]]

  implicitly[Leibniz[Nothing, Any, Int, Int]]
  implicitly[Leibniz[Int, Any, Int, Int]]
  implicitly[Leibniz[Int, AnyVal, Int, Int]]
  implicitly[Leibniz[Nothing, Any, AnyVal, AnyVal]]
  implicitly[Leibniz[Int, Any, AnyVal, AnyVal]]
  implicitly[Leibniz[Int, AnyVal, AnyVal, AnyVal]]
  implicitly[Leibniz[Nothing, Nothing, Nothing, Nothing]]

  implicitly[Int Iso Int]
  implicitly[Nothing Iso Nothing]
  implicitly[Any Iso Any]

  implicitly[Proposition[Proposition[0]]]
  implicitly[Proposition[0 === 1]]

//  Inhabited[0]
//  Inhabited["a"]

  SingletonOf[0, Int]

  Uninhabited[Void]
}