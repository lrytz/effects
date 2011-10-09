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
    else if (effectPolyMethods(sym.fullName)) Some(lattice.bottom)
    else None
  }

  def lookupExternalPC(sym: Symbol): Option[PCElem] = {
    if (isPureMethod(sym)) {
      Some(pcLattice.bottom)
    } else if (effectPolyMethods(sym.fullName)) {
      mkPC(sym)
    }
    else None
  }
  
  def mkPC(sym: Symbol): Some[pcLattice.PC] = {
    val param = sym.tpe match {
      case PolyType(_, MethodType(List(p), _)) => p
      case MethodType(List(p), _) => p
    }
    val fun = Some(param.tpe.member("apply"))
    val info = pcLattice.PCInfo(pcLattice.ParamLoc(param), fun)
    Some(pcLattice.PC(info))
  }
  
//  lazy val ExceptionClass = definitions.getClass("java.lang.Exception")
//  lazy val UnsupportedOperationExceptionClass = definitions.getClass("java.lang.UnsupportedOperationException")
//  lazy val NoSuchElementExceptionClass = definitions.getClass("java.util.NoSuchElementException")
  
  def isPureMethod(sym: Symbol) = {
    isValueClass(sym.owner) ||
    (sym.owner == StringClass) || // strings are immutable. @TODO: exclude methods on string that actually do have a side-effect!
    pureMethods(sym.fullName)
  }
  
  def isValueClass(sym: Symbol) = ScalaValueClasses.contains(sym)
  
  val pureMethods = Set(
    "java.lang.Object.<init>",
    
    "java.lang.Exception.<init>",
    "java.util.NoSuchElementException.<init>",
    "java.lang.UnsupportedOperationException.<init>",
    
    "scala.Some.apply",
    "scala.Option.isEmpty",
    "scala.Option.getOrElse"
  )
  
  val effectPolyMethods = Set[String](
  )
}
