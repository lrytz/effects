package effects

import java.io.IOException

// DDC splits it up into several, for example "Console", "FileSystem", "Network", ...

class IO extends Effect
object IO extends Effect

class noIO extends Effect
object noIO extends Effect

object IOTools {
  def read(file: String): String @IO @throws[IOException] = "..."
  def write(file: String, content: String): Unit @IO @throws[IOException] = ()
}

object Combine {
  import IOTools._


  /**
   * pure except for @IO. equivalent to "@IO @thorws[Nothing]" and "@IO @infer"
   */

  def getMyFile(): Option[String] @IO @pure =
    try {
      Some(read("myFile.txt"))
    } catch {
      case e: IOException => None
    }



}

