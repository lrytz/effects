name := "effects-plugin"

scalaHome in ThisBuild <<= baseDirectory { base =>
  Some(base / "lib/scala")
}

unmanagedBase <<= baseDirectory { base => base / "lib/scala/lib" }
