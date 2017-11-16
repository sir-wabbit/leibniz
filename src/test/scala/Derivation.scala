package leibniz

import leibniz.inhabitance.{Inhabited, Proposition, SingletonOf, Uninhabited}
import leibniz.internal.illTyped
import leibniz.variance.{Constant, Covariant, Injective, StrictlyCovariant}
import org.scalatest.{FunSuite, Matchers}

class Derivation extends FunSuite with Matchers {
  test("proposition") {
    implicitly[Proposition[Proposition[0]]]
    implicitly[Proposition[0 === 1]]
  }

  test("singleton of") {
    SingletonOf[0, Int]
  }

  test("equality") {
    implicitly[Void === Nothing]
  }

  test("inequality") {
    val int0 = 0
    val long0 = 0

    implicitly[0 =!= 1]
    implicitly[0 =!= 0L]
    implicitly[0 =!= "a"]
    implicitly[List[0] =!= List[1]]
    implicitly[List[1] =!= List[1L]]
    implicitly[Void =!= Any]
    implicitly[Void =!= Null]
    implicitly[Void =!= AnyRef]
    implicitly[Void =!= AnyVal]
    implicitly[Any =!= AnyRef]
    implicitly[Any =!= AnyVal]
    implicitly[AnyVal =!= AnyRef]
    implicitly[Int =!= Long]
    implicitly[Int =!= 0]

    implicitly[None.type =!= 0]

    // implicitly[Int =!= Int with Long]
  }

  test("strong inequality") {
    val int0 = 0
    val long0 = 0

    Apart[0, 1]
    Apart[0, 0L]
    Apart[0, "a"]
    Apart[List[0], List[1]]
    Apart[List[1], List[1L]]
    Apart[Void, Any]
    Apart[Void, Null]
    Apart[Void, AnyRef]
    Apart[Void, AnyVal]
    Apart[Any, AnyRef]
    Apart[Any, AnyVal]
    Apart[AnyVal, AnyRef]
    Apart[Int, Long]
    Apart[Int, 0]

    Apart[None.type, 0]

    // implicitly[Int =!= Int with Long]
  }

  test("concrete types") {
    ConcreteType[0]
    ConcreteType[Nothing]
    ConcreteType[Void]
    ConcreteType[Int]
    ConcreteType[String]
    ConcreteType[List[Option[Int]]]
    ConcreteType["abc"]
    ConcreteType[List["abc"]]
    ConcreteType[List[Array[Seq[Option[1]]]]]

    Eq[None.type]
    ConcreteType[None.type]

    // ConcreteType[Int with Any]
    // ConcreteType[(AnyRef { type Self = this.type }) with (Int { type Y })]
    // ConcreteType[i.type forSome { val i: X; type X }]
  }

  test("inhabitance") {
    Inhabited[Any]
    Inhabited[AnyVal]
    Inhabited[AnyRef]
    Inhabited[0]
    val x0: Int = 0
    Inhabited[x0.type]
    Inhabited[this.type] : Inhabited[this.type]
    Inhabited["abc"]
    Inhabited[Int]
    Inhabited[String]

    illTyped("Inhabited[Void]")
  }

  test("uninhabitance") {
    Uninhabited[Void]
    Uninhabited[Int => Void]

    illTyped("Uninhabited[Unit]")
  }

  test("injectivity") {
    // Constant type lambdas are not injective.
    illTyped("Injective[λ[x => List[Int]]]")
    illTyped("Injective[λ[x => Unit]]")

    // Identity is injective.
    Injective[λ[x => x]]
    Injective[({type L[x] = x})#L]

    { type f[x] = x; Injective[f] }

    { type f[+x] = x; Injective[f] }

    // (Class) type constructors are injective.
    Injective[Option]

    // Aliases to (class) type constructors are injective.
    Injective[List]

    Injective[Either[Int, ?]]

    // A more complex test.
    {
      type g[x, y] = List[(x, y)]
      type f[x] = g[x, x]
      implicitly[f[Int] === List[(Int, Int)]]
      Injective[f]
    }

    {
      type k[x] = Unit
      type f[x] = List[k[x]]
      implicitly[f[Int] === List[Unit]]
      illTyped("Injective[f]")
    }

    {
      type k[x] = Unit
      type h[x] = k[k[x]]
      type g[x, y] = List[h[x]]
      type f[x] = g[x, x]
      implicitly[f[Int] === List[Unit]]
      illTyped("Injective[f]")
    }

    def f[F[_]]: Unit = {
      illTyped("Injective[F]")
    }
  }

  test("covariance") {
    Covariant[Option]
    Covariant[List]
    Covariant[λ[`+x` => x]]
  }

  test("strict covariance") {
    StrictlyCovariant[Option]
    StrictlyCovariant[List]
    // StrictlyCovariant[λ[`+x` => x]]
  }
}
