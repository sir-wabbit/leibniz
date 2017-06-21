package leibniz

trait UnknownInt {
  type T
  type K[_]
}
final class UnknownImpl extends UnknownInt {
  type T    = Any
  type K[_] = Any
}