package leibniz

abstract class FunctionK[-A[_], +B[_]] { ab =>
  def run(a: A[Unk]): B[Unk]
  final def apply[X](ax: A[X]): B[X] =
    run(ax.asInstanceOf[A[Unk]]).asInstanceOf[B[X]]
  final def andThen[C[_]](bc: FunctionK[B, C]): FunctionK[A, C] =
    a => bc.run(ab.run(a))
  final def compose[Z[_]](za: FunctionK[Z, A]): FunctionK[Z, B] =
    z => ab.run(za.run(z))
}
object FunctionK {
  def id[A[_]]: FunctionK[A, A] = a => a
}

abstract class FunctionK2[-A[_, _], +B[_, _]] { ab =>
  def run(a: A[Unk1, Unk2]): B[Unk1, Unk2]
  final def apply[X, Y](ax: A[X, Y]): B[X, Y] =
    run(ax.asInstanceOf[A[Unk1, Unk2]]).asInstanceOf[B[X, Y]]
  final def andThen[C[_, _]](bc: FunctionK2[B, C]): FunctionK2[A, C] =
    a => bc.run(ab.run(a))
  final def compose[Z[_, _]](za: FunctionK2[Z, A]): FunctionK2[Z, B] =
    z => ab.run(za.run(z))
}
object FunctionK2 {
  def id[A[_, _]]: FunctionK2[A, A] = a => a
}

abstract class FunctionK3[-A[_, _, _], +B[_, _, _]] { ab =>
  def run(a: A[Unk1, Unk2, Unk3]): B[Unk1, Unk2, Unk3]
  final def apply[X, Y, Z](ax: A[X, Y, Z]): B[X, Y, Z] =
    run(ax.asInstanceOf[A[Unk1, Unk2, Unk3]]).asInstanceOf[B[X, Y, Z]]
  final def andThen[C[_, _, _]](bc: FunctionK3[B, C]): FunctionK3[A, C] =
    a => bc.run(ab.run(a))
  final def compose[Z[_, _, _]](za: FunctionK3[Z, A]): FunctionK3[Z, B] =
    z => ab.run(za.run(z))
}
object FunctionK3 {
  def id[A[_, _, _]]: FunctionK3[A, A] = a => a
}

abstract class FunctionK4[-A[_, _, _, _], +B[_, _, _, _]] { ab =>
  def run(a: A[Unk1, Unk2, Unk3, Unk4]): B[Unk1, Unk2, Unk3, Unk4]
  final def apply[X, Y, Z, W](ax: A[X, Y, Z, W]): B[X, Y, Z, W] =
    run(ax.asInstanceOf[A[Unk1, Unk2, Unk3, Unk4]]).asInstanceOf[B[X, Y, Z, W]]
  final def andThen[C[_, _, _, _]](bc: FunctionK4[B, C]): FunctionK4[A, C] =
    a => bc.run(ab.run(a))
  final def compose[Z[_, _, _, _]](za: FunctionK4[Z, A]): FunctionK4[Z, B] =
    z => ab.run(za.run(z))
}
object FunctionK4 {
  def id[A[_, _, _, _]]: FunctionK4[A, A] = a => a
}