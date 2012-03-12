name := "effects-plugin"

scalaHome in ThisBuild <<= baseDirectory { base =>
  Some(base / "lib/scala")
}

scalaVersion := "scala-effects"

libraryDependencies := Seq()

unmanagedBase <<= baseDirectory { base => base / "lib/scala/lib" }
