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

  val throwsClass = definitions.getClass("scala.annotation.effects.exceptions.throws")
  val scalaThrowsClass = definitions.getClass("scala.throws")
  val annotationClasses = List(throwsClass)
  
  val barTrait = definitions.getClass("scala.annotation.effects.exceptions.$bar")

  
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

  def toAnnotation(elem: Elem): AnnotationInfo = {
    def toType(elem: Elem): Type = elem match {
      case Nil => lattice.nothingType
      case x :: Nil => x
      case x :: xs => typeRef(barTrait.tpe.prefix, barTrait, List(x, toType(xs)))
    }
    AnnotationInfo(typeRef(throwsClass.tpe.prefix, throwsClass, List(toType(elem))), Nil, Nil)
  }
  
  override def newEffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): EffectTraverser =
    new ExceptionsTraverser(tree, typer, owner, unit)
  
  /**
   * A method which computes the effect of a Tree. Note that this doesn't exist in the superclass
   * (EffectChecker), there `computeEffect` can only be called for a Symbol. The reason:
   * 
   * @TODO: this is maybe not very correct: effect traversers expect trees that went through
   * "refine", see comment in checkDefDef.
   * But we can't really call the "refine" traverser here, because we don't know what to do with
   * the resulting transformed tree - the "transformed" map only maps symbols to transformed trees,
   * not arbitrary subtrees.
   */
  def computeEffect(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): Elem = {
    newEffectTraverser(tree, typer, owner, unit).compute()
  }

  class ExceptionsTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit) extends EffectTraverser(tree, typer, owner, unit) {
    override def traverse(tree: Tree) {
      tree match {
        case Throw(expr) =>
          traverse(expr)
          add(List(expr.tpe))

        case Try(body, catches, finalizer) =>
          val bodyEff = computeEffect(body, typer, owner, unit)
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
            catchEff = lattice.join(catchEff, computeEffect(body, typer, owner, unit))
          }
          val bodyMasked = lattice.mask(bodyEff, mask)
          val finEff = computeEffect(finalizer, typer, owner, unit)
          add(bodyMasked)
          add(catchEff)
          add(finEff)

        case _ =>
          super.traverse(tree)
      }
    }
  }


}