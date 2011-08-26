package scala.tools.nsc.effects

trait ExternalEffects[L <: CompleteLattice] { this: EffectChecker[L] =>
  import global._
  import definitions._
  import analyzer.Context
  import lattice.Elem
  import pcLattice.{Elem => PCElem}
  
  /**
   * @TODO: it would probably be better to return annotations, not effects of
   * external symbols. that way we could support external annotations later.
   */
  def lookupExternal(sym: Symbol): Option[Elem] = {
    if (isPureMethod(sym)) Some(lattice.bottom)
    else None
  }

  def lookupExternalPC(sym: Symbol): Option[PCElem] = {
    if (isPureMethod(sym)) Some(pcLattice.bottom)
    else None
  }
  
  val ExceptionClass = definitions.getClass("java.lang.Exception")
  
  def isPureMethod(sym: Symbol) = {
    isValueClass(sym.owner) ||
    (sym.isConstructor && sym.owner == ObjectClass) ||
    (sym.owner == ExceptionClass) ||
    (sym.owner == StringClass) // strings are immutable. @TODO: exclude methods on string that actually do have a side-effect!
  }
  
  def isValueClass(sym: Symbol) = ScalaValueClasses.contains(sym)
}
