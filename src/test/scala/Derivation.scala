package leibniz

import leibniz.inhabitance.{Inhabited, Proposition, SingletonOf, Uninhabited}
import leibniz.internal.illTyped
import leibniz.variance._
import org.scalatest.{FunSuite, Matchers}

class Derivation extends FunSuite with Matchers {
  test("proposition") {
    implicitly[Proposition[Proposition[0]]]
    implicitly[Proposition[0 === 1]]
    implicitly[Proposition[Inhabited[0]]]
    implicitly[Proposition[Inhabited[Void]]]
  }

  test("singleton of") {
    SingletonOf[0, 0]
    SingletonOf[0, Int]
    SingletonOf[0, AnyVal]
    SingletonOf[0, Any]
    SingletonOf[None.type, None.type]
    SingletonOf[None.type, Option[Int]]
    SingletonOf[None.type, Option[String]]
  }

  test("equality") {
    implicitly[Void === Nothing]

    object Test {
      type AnyLike >: Any
      implicitly[AnyLike === Any]
    }

    val i: 0 = 0
    val j: i.type = i
    implicitly[0 === i.type]
    implicitly[j.type === i.type]

    implicitly[Int === Int]
    implicitly[Nothing === Nothing]
    implicitly[Any === Any]
    implicitly[0 === 0]
    implicitly["" === ""]

    illTyped("implicitly[1 === 0]")
    illTyped("implicitly[Null === Void]")
    illTyped("implicitly[Any === Void]")
    illTyped("implicitly[AnyRef === Any]")

    type g[x] = Unit
    type h[x] = g[g[x]]
    type f[x] = List[h[x]]
    implicitly[f[Int] === List[Unit]]
  }

  test("hk equality") {
    type Id[x] = x
    implicitly[List =~= List]
    implicitly[Id =~= Id]
    implicitly[Either[Int, ?] =~= Either[Int, ?]]
    implicitly[(Int => ?) =~= (Int => ?)]

    // implicitly[(? => Int) =~= (? => Int)]
  }

  test("f-bounded equality") {
    //  trait Nat[X <: Nat[X]]
    //  final case class Z() extends Nat[Z]
    //  final case class S[N](n: N) extends Nat[S[N]]
    //  implicitly[IsF[Nat, Z, Z]]
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

    illTyped("implicitly[0 =!= 0]")
    illTyped("implicitly['a =!= 'a]")
    illTyped("implicitly[(Int with String) =!= (String with Int)]")
    illTyped("implicitly[Int =!= Int]")

    type g[x] = Unit
    type h[x] = g[g[x]]
    type f[x] = List[h[x]]
    illTyped("implicitly[List[Unit] =!= f[Int]]")
    // implicitly[Int =!= Int with Long]
  }

  test("liskov simple") {
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

    implicitly[(String, Int) <~< (String, Any)]
    implicitly[(String, Int) <~< (Any, Any)]
    implicitly[(String, Int) <~< (AnyRef, AnyVal)]
    implicitly[(String, Int) <~< AnyRef]
    implicitly[(String, Int) <~< Any]
    implicitly[Null <~< (String, Int)]
    implicitly[Nothing <~< (String, Int)]

    implicitly[Int As1 AnyVal]
  }

  test("complex === and <~<") {
    trait A { type X }
    def f1(a: A): a.X === a.X = implicitly[Is[a.X, a.X]]
    def f2(a: A): a.X <~< a.X = implicitly[As[a.X, a.X]]
    def f3(a: A): As1[a.X, a.X] = implicitly[As1[a.X, a.X]]

    trait F[L, H >: L] { type A >: L <: (H with B); type B >: L <: H }
    def g1[L, H >: L](a: F[L, H]): Is[a.A, a.A] = implicitly[Is[a.A, a.A]]
    def g2[L, H >: L](a: F[L, H]): As[a.A, a.B] = implicitly[As[a.A, a.B]]
    def g3[L, H >: L](a: F[L, H]): As[a.A, a.B] = implicitly[As[a.A, a.B]]

    def h1[A, B >: A]: As[A, B] = implicitly[As[A, B]]
    def h2[A]: Is[A, A] = implicitly[Is[A, A]]
    def h3[A]: As[A, A] = implicitly[As[A, A]]
  }

  test("bounded") {
    implicitly[Bounded[Nothing, AnyVal, Int]]
    implicitly[Bounded[Int, AnyVal, Int]]
    implicitly[Bounded[Nothing, Int, Int]]
    implicitly[Bounded[Int, Int, Int]]
  }

  test("liskov") {
    implicitly[Liskov[Nothing, Any, Int, AnyVal]]
    implicitly[Liskov[Int, Any, Int, AnyVal]]
    implicitly[Liskov[Int, AnyVal, Int, AnyVal]]
  }

  test("liskov1") {
    implicitly[Liskov1[Nothing, Any, Int, AnyVal]]
    implicitly[Liskov1[Int, Any, Int, AnyVal]]
    implicitly[Liskov1[Int, AnyVal, Int, AnyVal]]
  }

  test("liskov2") {
    implicitly[Liskov2[Nothing, Any, Int, AnyVal]]
    implicitly[Liskov2[Int, Any, Int, AnyVal]]
    implicitly[Liskov2[Int, AnyVal, Int, AnyVal]]
  }

  test("leibniz") {
    implicitly[Leibniz[Nothing, Any, Int, Int]]
    implicitly[Leibniz[Int, Any, Int, Int]]
    implicitly[Leibniz[Int, AnyVal, Int, Int]]
    implicitly[Leibniz[Nothing, Any, AnyVal, AnyVal]]
    implicitly[Leibniz[Int, Any, AnyVal, AnyVal]]
    implicitly[Leibniz[Int, AnyVal, AnyVal, AnyVal]]
    implicitly[Leibniz[Nothing, Nothing, Nothing, Nothing]]
  }

  test("iso") {
    implicitly[Int Iso Int]
    implicitly[Nothing Iso Nothing]
    implicitly[Any Iso Any]
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

    // Apart[None.type, 0]

    // implicitly[Int =!= Int with Long]
  }

  test("concrete types") {
    TypeId[0]
    TypeId[Nothing]
    TypeId[Void]
    TypeId[Int]
    TypeId[String]
    TypeId[List[Option[Int]]]
    TypeId["abc"]
    TypeId[List["abc"]]
    TypeId[List[Array[Seq[Option[1]]]]]

    // Eq[None.type]
    // TypeId[None.type]

    // ConcreteType[Int with Any]
    // ConcreteType[(AnyRef { type Self = this.type }) with (Int { type Y })]
    // ConcreteType[i.type forSome { val i: X; type X }]
  }

  test("type id comparisons") {
    val types: Array[TypeId[_]] = Array(
      TypeId[0],
      TypeId[0L],
      TypeId[1],
      TypeId[Nothing],
      TypeId[Int],
      TypeId[String],
      TypeId[List[Option[Int]]],
      TypeId["abc"],
      TypeId["cde"],
      TypeId[List["abc"]],
      TypeId[List[Array[Seq[Option[1]]]]]
    )

    for (i <- types.indices; j <- types.indices) {
//      println(s"$i $j ${types(i)} ${types(j)}")
      if (i == j) (types(i) compare types(j)).isRight should be (true)
      else (types(i) compare types(j)).isRight should be (false)
    }


    // Eq[None.type]
    // TypeId[None.type]

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
    Uninhabited[Int => String => Void]
    // Uninhabited[(Int => String) => Void]

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
    // Covariant[λ[`+x` => x]]
  }

  test("strict covariance") {
    StrictlyCovariant[Option]
    StrictlyCovariant[List]
    // StrictlyCovariant[λ[`+x` => x]]
  }

  test("contravariance") {
    type f[-x] = x => Boolean
    Contravariant[f]
  }

  test("strict contravariance") {
    type f[-x] = x => Boolean
    // StrictlyContravariant[f]
  }

  test("implies") {
    Implies[Inhabited[Int], Inhabited[Inhabited[Int]]]
    implicitly[Inhabited[Int] |- Uninhabited[Uninhabited[Int]]]

    implicitly[Unit |- Inhabited[Any]]

    illTyped("implicitly[Unit |- Inhabited[Void]]")

    {
      trait Monoid[M] {
        def empty: M
        def combine(a: M, b: M): M
      }
      trait CMonoid[M] extends Monoid[M]

      trait Foldable[F, T[_]] {
        type Type
        def foldMap[B](ft: F)(f: Type => B)(implicit B: T[B]): B
      }

      implicit def foldable[F, T1[_], T2[x] <: T1[x]]
      (implicit T1: Foldable[F, T1]): Foldable[F, T2] { type Type = T1.Type } =
        new Foldable[F, T2] {
          type Type = T1.Type
          def foldMap[B](ft: F)(f: Type => B)(implicit B: T2[B]): B = T1.foldMap[B](ft)(f)(B: T1[B])
        }

      implicit def listFoldable[A]: Foldable[List[A], Monoid] =
        new Foldable[List[A], Monoid] {
          type Type = A
          def foldMap[B](ft: List[A])(f: A => B)(implicit B: Monoid[B]): B =
            ft.map(f).foldLeft(B.empty)(B.combine)
        }

      implicitly[Foldable[List[Int], CMonoid]]
    }
  }

  test("forall") {
    type f[x] = Inhabited[Int]
    Forall[f]

    Forall[λ[x => Inhabited[Int]]]

    trait Foo[A]
    implicit def foo[A]: Foo[A] = new Foo[A] { }

    Forall[Foo]
    Forall[λ[x => Foo[(x, x)]]]

    type g[x] = Inhabited[x] |- Inhabited[Inhabited[x]]
    Forall[g]

//    Forall[({type L[x] = Inhabited[x] |- Inhabited[Inhabited[x]]})#L]

//    {
//      trait Monoid[M] {
//        def empty: M
//        def combine(a: M, b: M): M
//      }
//      trait CMonoid[M] extends Monoid[M]
//
//      trait Foldable[F, T[_]] {
//        type Type
//        def foldMap[B](ft: F)(f: Type => B)(implicit B: T[B]): B
//      }
//
//      type ImpliesK[T1[_], T2[_], A] = T1[A] |- T2[A]
//      type Test[T1[_], T2[_]] = Forall[ImpliesK[T2, T1, ?]]
//
//      implicit def foldable[F, T1[_], T2[_]]
//      (implicit T1: Foldable[F, T1], ev: Test[T1, T2]): Foldable[F, T2] { type Type = T1.Type } =
//        new Foldable[F, T2] {
//          type Type = T1.Type
//          def foldMap[B](ft: F)(f: Type => B)(implicit B: T2[B]): B = T1.foldMap[B](ft)(f)(ev.apply[B](B))
//        }
//
//      implicit def listFoldable[A]: Foldable[List[A], Monoid] =
//        new Foldable[List[A], Monoid] {
//          type Type = A
//          def foldMap[B](ft: List[A])(f: A => B)(implicit B: Monoid[B]): B =
//            ft.map(f).foldLeft(B.empty)(B.combine)
//        }
//
//      implicitly[Foldable[List[Int], CMonoid]]
//    }
  }
}
