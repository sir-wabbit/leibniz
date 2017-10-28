package leibniz

trait Pi[-T, +F[_]] {
  def apply(x: T): F[x.type]
}
