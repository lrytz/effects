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
    // early def: the EffectInferencer constructor accesses "checker.global"
    val checker = pcChecker
  } with pc.PCInferencer {
    val runsAfter = List("superaccessors")
    val phaseName = "pcInferencer"
  }

/*
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
 */

  val stateChecker = new state.StateChecker(global)
  val stateInferencer = new {
    val checker = stateChecker
  } with state.StateInferencer {
    val runsAfter = List("pcChecker")
    val phaseName = "stateInferencer"
  }

  /**
   * The compiler components that will be applied when running this plugin
   */
  val components = List(pcInferencer, pcChecker, stateChecker, stateInferencer /*, simpleInferencer, simpleChecker, exceptionsInferencer, exceptionsChecker */ /* , xioInferencer, xioChecker */)
}

object EffectsPlugin {
  var logPcall = false
  var logExc = false
}
