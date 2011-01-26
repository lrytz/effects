import sbt._

class EffectsPlugin(info: ProjectInfo) extends DefaultProject(info) {
  val scalaDir = "lib/scala"

  override def localScala =
    defineScala("effects-scala", new java.io.File(scalaDir)) :: Nil
}
