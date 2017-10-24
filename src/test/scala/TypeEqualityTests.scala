package leibniz

class TypeEqualityTests {
  final val int0 = 0
  final val long0 = 0

  implicitly[Void === Nothing]
  implicitly[0 =!= 1]
  implicitly[0 =!= 0L]
  implicitly[0 =!= "a"]
  implicitly[0 === int0.type]
  implicitly[0 === long0.type]
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
  // implicitly[Int =!= Int with Long]
  implicitly[Int === Int {}]
  ConcreteType[List[Array[Seq[Option[1]]]]]
  ConcreteType[Int with Any]
  // ConcreteType[(AnyRef { type Self = this.type }) with (Int { type Y })]
  // ConcreteType[i.type forSome { val i: X; type X }]
  ConcreteType[0]
  // ConcreteType[None.type]
}
