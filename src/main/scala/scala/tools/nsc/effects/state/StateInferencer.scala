package scala.tools.nsc.effects
package state

trait StateInferencer extends EffectInferencer[StateLattice] {
  val checker: StateChecker
  
  import checker._
  import global._
  
  import lattice.{StoreLoc, AssignLoc, LocSet, ThisLoc, SymLoc, Fresh, mkElem}

  override def getterEffect(sym: Symbol): Elem = {
    val owner = sym.owner
    val loc = {
      if (owner.isModuleClass) SymLoc(owner.sourceModule)
      else ThisLoc(owner)
    }
    // for abstract fields, there is no field symbol. so we check the annotation on the getter.
    if (atPhase(currentRun.typerPhase)(sym.hasAnnotation(localClass))) {
      mkElem(LocSet(loc))
    } else {
      lattice.pure
    }
  }

  override def setterEffect(sym: Symbol): Elem = {
    val owner = sym.owner
    val loc = {
      if (owner.isModuleClass) SymLoc(owner.sourceModule) // @TODO: modules should just be considered global state (right? or, what about nested modules? those probably not...)
      else ThisLoc(owner)
    }
    // for abstract fields, there is no field symbol. so we check the annotation on the getter.
    val getter = sym.getter(sym.owner)
    if (atPhase(currentRun.typerPhase)(getter.hasAnnotation(localClass))) {
      val List(List(arg)) = sym.paramss
      mkElem(StoreLoc(loc, LocSet(SymLoc(arg))))
    } else {
      mkElem(StoreLoc(loc, LocSet(Fresh)))
    }
  }
}
