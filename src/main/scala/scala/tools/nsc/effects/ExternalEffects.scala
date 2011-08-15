package scala.tools.nsc.effects

import scala.tools.nsc._

trait ExternalEffects[L <: CompleteLattice] { this: EffectChecker[L] =>
  import global._
  import definitions._
  import analyzer.Context
  
  /**
   * @TODO: it would be better to return annotations, not effects of external
   * symbols. that way we could support external annotations later.
   */
  def lookupExternal(sym: Symbol, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Option[Elem] = {
    if (isPureMethod(sym)) Some(lattice.bottom)
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
