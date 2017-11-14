package leibniz

trait Pi[-T, +F[_]] {
  def apply(x: T): F[x.type]
}
object Pi {
  def id[T]: Pi[T, λ[x => x]] = new Pi[T, λ[x => x]] {
    override def apply(x: T): x.type = x
  }
}