package leibniz


object MacroTest {
  def run[A]: Unit = macro internal.MacroUtil.info[A]
}
