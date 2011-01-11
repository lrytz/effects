import sbt._

class EffectsPlugin(info: ProjectInfo) extends DefaultProject(info) {
  val nightlyDir = "/Users/luc/scala/nightly/"

  override def localScala =
    defineScala("2.9.0-nightly", new java.io.File(nightlyDir)) :: Nil
}
