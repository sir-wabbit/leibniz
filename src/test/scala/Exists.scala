import org.scalatest.FunSpec

import leibniz._

class ExistsTest extends FunSpec {
  trait Show[A] {
    def show(a: A): String
  }
  type Showable0[X] = (X, Show[X])
  type Showable = Exists[Showable0]

  def test(s: Showable): String = {
    val x = Exists.unwrap[Showable0](s)
    x._2.show(x._1)

    // This line doesn't work in IJ.
    s.value._2.show(s.value._1)
  }
}
