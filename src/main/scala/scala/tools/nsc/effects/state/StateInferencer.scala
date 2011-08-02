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
    val field = sym.accessed
    if (field.hasAnnotation(localClass)) {
      mkElem(LocSet(loc))
    } else {
      lattice.pure
    }
  }

  override def setterEffect(sym: Symbol): Elem = {
    val owner = sym.owner
    val loc = {
      if (owner.isModuleClass) SymLoc(owner.sourceModule)
      else ThisLoc(owner)
    }
    val field = sym.accessed
    if (field.hasAnnotation(localClass)) {
      val List(List(arg)) = sym.paramss
      mkElem(StoreLoc(loc, LocSet(SymLoc(arg))))
    } else {
      mkElem(StoreLoc(loc, LocSet(Fresh)))
    }
  }
}
