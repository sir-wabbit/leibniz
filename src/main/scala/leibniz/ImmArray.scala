package leibniz

import leibniz.macros.newtype

@newtype final case class ImmArray[A](unsafeValue: Array[A]) {
  def length: Int = unsafeValue.length
}
