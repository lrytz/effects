package scala.tools.nsc.effects

import scala.tools.nsc.Global
import scala.tools.nsc.plugins.Plugin

class EffectsPlugin(val global: Global) extends Plugin {
  /** The name of this plugin. */
  val name = "effects"

  /** A short description of the plugin */
  val description = "tracks side effects"

  /** A description of the plugin's options */
  override val optionsHelp =
    Some("  -P:"+ name +":log-exc        show the inferred exceptions of methods\n"+
         "  -P:"+ name +":log-pcall      show the inferred parameter calls of methods")

  /** parsing of plugin options */
  override def processOptions(options: List[String], error: String => Unit) {
    val rest = new collection.mutable.ListBuffer[String]()
    for (o <- options) {
      if (o == "log-exc")
        EffectsPlugin.logExc = true
      else if (o == "log-pcall")
        EffectsPlugin.logPcall = true
      else
        rest += o
    }
    super.processOptions(rest.toList, error)
  }

  val pcChecker = new pc.PCChecker(global)
  val pcInferencer = new {
    val checker = pcChecker
  } with EffectInferencer[pc.PCLattice] {
    val runsAfter = List("superaccessors")
    val phaseName = "pcInferencer"
  }

  val simpleChecker = new simple.SimpleChecker(global)
  val simpleInferencer = new {
    val checker = simpleChecker
  } with EffectInferencer[simple.SimpleLattice] {
    val runsAfter = List("pcChecker")
    val phaseName = "simpleInferencer"
  }

  val xioChecker = new xio.XioChecker(global)
  val xioInferencer = new {
    val checker = xioChecker
  } with EffectInferencer[xio.XioLattice] {
    val runsAfter = List("simpleChecker")
    val phaseName = "xioInferencer"
  }

  val exceptionsChecker = new exceptions.ExceptionsChecker(global)
  val exceptionsInferencer = new {
    val checker = exceptionsChecker
  } with EffectInferencer[exceptions.ExceptionsLattice] {
    val runsAfter = List("simpleChecker")
    val phaseName = "exceptionsInferencer"
  }
 
  /*
  val paramCallsChecker = new ParamCallsChecker(global)
  val paramCallsInferencer = new {
    val checker = paramCallsChecker
  } with EffectInferencer[ParamCalls] {
    val runsAfter = List("superaccessors")
    val phaseName = "paramcallsinferencer"
  }
*/

/*
  val exceptionsChecker = new ExceptionsChecker(global)
  val exceptionsInferencer = new {
    // early def: the EffectInferencer constructor accesses "checker.global"
    val checker = exceptionsChecker
  } with EffectInferencer[Exceptions] {
    val runsAfter = List("paramcallschecker")
    val phaseName = "exceptionsinferencer"
  }
*/

  /**
   * The compiler components that will be applied when running this plugin
   */
  val components = List(pcInferencer, pcChecker, simpleInferencer, simpleChecker /*, exceptionsInferencer, exceptionsChecker */ /* , xioInferencer, xioChecker */)
  // List(paramCallsInferencer, paramCallsChecker, exceptionsInferencer, exceptionsChecker)

}

object EffectsPlugin {
  var logPcall = false
  var logExc = false
}
