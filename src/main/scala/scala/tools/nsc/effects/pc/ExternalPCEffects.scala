/*
package scala.tools.nsc.effects
package pc


trait ExternalPCEffects[L <: CompleteLattice] { this: PCTracking[L] with ExternalEffects[L] =>
  import global._
  import analyzer.Context
  import pcCommons._

  /**
   */
  def lookupExternalPC(sym: Symbol): Option[pcLattice.Elem] = {
    if (isPureMethod(sym)) Some(pcLattice.bottom)
    else None
  }
}
*/