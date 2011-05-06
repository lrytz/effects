package scala.tools.nsc.effects
package state

import scala.tools.nsc._
import scala.collection.{immutable => i}

class StateChecker(val global: Global) extends EffectChecker[StateLattice] {
  import global._
  import analyzer.Typer

  val runsAfter = List("stateInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "stateChecker"

  val lattice = new StateLattice {
    val global: StateChecker.this.global.type = StateChecker.this.global
  }
  import lattice.{Mod, ModAll, Loc, NonLoc}

  val modClass = definitions.getClass("scala.annotation.effects.state.mod")
  val modAllClass = definitions.getClass("scala.annotation.effects.state.modAll")
  val locClass = definitions.getClass("scala.annotation.effects.state.loc")
  val nonLocClass = definitions.getClass("scala.annotation.effects.state.nonLoc")
  val localClass = definitions.getClass("scala.annotation.effects.state.local")

  val annotationClasses = List(modClass, modAllClass, locClass, nonLocClass)

  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem] = {
    val locAnn = annots.filter(_.atp.typeSymbol == locClass).headOption
    locAnn.map(m => (Mod(), Loc(m.args.map(_.symbol).toSet))) orElse {
      val modAllAnn = annots.filter(_.atp.typeSymbol == modAllClass).headOption
      modAllAnn.map(_ => (ModAll, NonLoc)) orElse {
        val modAnn = annots.filter(_.atp.typeSymbol == modClass).headOption
        modAnn.map(m => {
          (Mod(m.args.map(_.symbol).toSet), NonLoc)
        }) orElse {
          val pureAnn = annots.filter(_.atp.typeSymbol == pureAnnotation).headOption
          pureAnn.map(_ => (Mod(), NonLoc))
        }
      }
    }
  }

  def toAnnotation(elem: Elem): AnnotationInfo = elem match {
    case (_, Loc(locations)) => AnnotationInfo(locClass.tpe, locations.toList.map(Ident(_)), Nil)
    case (Mod(locations), _) => AnnotationInfo(modClass.tpe, locations.toList.map(Ident(_)), Nil)
    case (ModAll, _) => AnnotationInfo(modAllClass.tpe, Nil, Nil)
  }

  override def newEffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(tree, typer, owner, unit)

  class StateTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit) extends EffectTraverser(tree, typer, owner, unit) {

    var env: i.Map[Symbol, i.Set[Symbol]] = Map()
    
    def localityOf(tree: Tree): i.Set[Symbol] = Set()
    
    override def traverse(tree: Tree) {
      tree match {
        case ValDef(_, _, _, rhs) =>
          env = env.updated(tree.symbol, localityOf(rhs))
          
        case _ =>
          super.traverse(tree)
      }
    }
  }
}