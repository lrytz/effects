package scala.tools.nsc.effects
package exceptions

import scala.tools.nsc._

class ExceptionsChecker(val global: Global) extends EffectChecker[ExceptionsLattice] {
  import global._
  import analyzer.Typer

  val runsAfter = List("exceptionsInferencer")
  override val runsBefore = List("pickler")
  val phaseName = "exceptionsChecker"

  val lattice = new ExceptionsLattice {
    val global: ExceptionsChecker.this.global.type = ExceptionsChecker.this.global
  }
  import lattice.Elem

  val throwsClass = definitions.getRequiredClass("scala.annotation.effects.exceptions.throws")
  val scalaThrowsClass = definitions.getRequiredClass("scala.throws")
  val annotationClasses = List(throwsClass)
  
  val barTrait = definitions.getRequiredClass("scala.annotation.effects.exceptions.$bar")

  
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem] = {
    def exceptionsOf(tp: Type): List[Type] = tp match {
      case TypeRef(pre, `barTrait`, args) =>
        args.flatMap(exceptionsOf)
      case tp =>
        List(tp)
    }

    val throwsAnn = annots.filter(_.atp.typeSymbol == throwsClass)
    if (!throwsAnn.isEmpty) {
      Some(((Nil: Elem) /: throwsAnn)((elem, annot) => {
        val TypeRef(_, _, List(arg)) = annot.atp
        lattice.join(elem, exceptionsOf(arg))
      }))
    } else {
      val pureAnnot = annots.filter(_.atp.typeSymbol == pureAnnotation).headOption
      pureAnnot.map(_ => lattice.bottom)
    }

    /* {
      val scalaThrowsAnn = annots.filter(_.atp.typeSymbol == scalaThrowsClass)
      if (scalaThrowsAnn.isEmpty) None
      else Some(((Nil: Elem) /: scalaThrowsAnn)((elem, annot) =>
        annot.args match {
          case Literal(const) :: Nil =>
            lattice.join(elem, List(const.typeValue))
          case _ =>
            abort("unexpected throws annotation: "+ annot)
        }
      ))
    }*/
  }

  def toAnnotation(elem: Elem): List[AnnotationInfo] = {
    def toType(elem: Elem): Type = elem match {
      case Nil => lattice.nothingType
      case x :: Nil => x
      case x :: xs => typeRef(barTrait.tpe.prefix, barTrait, List(x, toType(xs)))
    }
    List(AnnotationInfo(typeRef(throwsClass.tpe.prefix, throwsClass, List(toType(elem))), Nil, Nil))
  }
  
  override def newEffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): EffectTraverser =
    new ExceptionsTraverser(tree, typer, owner, unit)

  class ExceptionsTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit) extends EffectTraverser(tree, typer, owner, unit) {
    override def traverse(tree: Tree) {
      tree match {
        case Throw(expr) =>
          traverse(expr)
          add(List(expr.tpe))

        case Try(body, catches, finalizer) =>
          val bodyEff = subtreeEffect(body)
          var mask: Elem = lattice.bottom
          var catchEff: Elem = lattice.bottom
          for (CaseDef(pat, guard, body) <- catches) {
            pat match {
              case Bind(_, Typed(Ident(nme.WILDCARD), tpt)) if guard.isEmpty =>
                mask = lattice.join(mask, List(tpt.tpe))
              case Typed(Ident(nme.WILDCARD), tpt) if guard.isEmpty =>
                mask = lattice.join(mask, List(tpt.tpe))
              case _ =>
                ()
            }
            // @TODO guards are expected to be effect-free (assert that!)
            catchEff = lattice.join(catchEff, subtreeEffect(body))
          }
          val bodyMasked = lattice.mask(bodyEff, mask)
          val finEff = subtreeEffect(finalizer)
          add(bodyMasked)
          add(catchEff)
          add(finEff)

        case _ =>
          super.traverse(tree)
      }
    }
  }


}