package leibniz

abstract class FunctionK[-A[_], +B[_]] { ab =>
  def run(a: A[:?:]): B[:?:]

  final def apply[X](ax: A[X]): B[X] =
    run(ax.asInstanceOf[A[:?:]]).asInstanceOf[B[X]]

  final def andThen[C[_]](bc: FunctionK[B, C]): FunctionK[A, C] =
    a => bc.run(ab.run(a))

  final def compose[Z[_]](za: FunctionK[Z, A]): FunctionK[Z, B] =
    z => ab.run(za.run(z))
}
object FunctionK {
  def id[A[_]]: FunctionK[A, A] = a => a
}
