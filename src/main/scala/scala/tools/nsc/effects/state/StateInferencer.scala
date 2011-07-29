package scala.tools.nsc.effects
package state

abstract class StateInferencer extends EffectInferencer[StateLattice] {
  val checker: StateChecker
  
  import checker._
  import global._
  
  import lattice.{StoreLoc, AssignLoc, LocSet, ThisLoc, SymLoc, Fresh}

  override def getterEffect(sym: Symbol): Elem = {
    val field = sym.accessed
    if (field.hasAnnotation(localClass)) {
      (StoreLoc(), AssignLoc(), LocSet(ThisLoc(sym.owner)))
    } else {
      lattice.pure
    }
  }

  override def setterEffect(sym: Symbol): Elem = {
    val field = sym.accessed
    if (field.hasAnnotation(localClass)) {
      val List(List(arg)) = sym.paramss
      (StoreLoc(ThisLoc(sym.owner), LocSet(SymLoc(arg))), AssignLoc(), LocSet())
    } else {
      (StoreLoc(ThisLoc(sym.owner), LocSet(Fresh)), AssignLoc(), LocSet())
    }
  }
}
