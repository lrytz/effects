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
  import lattice.{Locality, AnyLoc, LocSet,
                  Location, SymLoc, Fresh, ThisLoc,
                  Store, StoreAny, StoreLoc,
                  Assignment, AssignAny, AssignLoc,
                  join, joinStore, joinAssignment, joinLocality}

  /* Annotation Classes */
  val modClass = definitions.getClass("scala.annotation.effects.state.mod")
  val storeClass = definitions.getClass("scala.annotation.effects.state.store")
  val assignStrongClass = definitions.getClass("scala.annotation.effects.state.assignStrong")
  val assignClass = definitions.getClass("scala.annotation.effects.state.assign")
  val locClass = definitions.getClass("scala.annotation.effects.state.loc")

  val localClass = definitions.getClass("scala.annotation.effects.state.local")

  val annotationClasses = List(modClass, storeClass, assignStrongClass, assignClass, locClass)

  
  /* Locations */
  val anyLocObject = definitions.getModule("scala.annotation.effects.state.any")
  val freshLocObject = definitions.getModule("scala.annotation.effects.state.fresh")
  
  
  def fromAnnotation(annots: List[AnnotationInfo]): Option[Elem] = {
    
    def locationOf(arg: Tree): Option[Either[Location, AnyLoc.type]] = arg match {
      case This(_)  =>
        Some(Left(ThisLoc(arg.symbol)))
      case Ident(_) =>
        if (arg.symbol == anyLocObject) Some(Right(AnyLoc))
        else if (arg.symbol == freshLocObject) Some(Left(Fresh))
        else Some(Left(SymLoc(arg.symbol)))
      case Select(_, _) if (arg.symbol == anyLocObject) =>
        Some(Right(AnyLoc))
      case Select(_, _) if (arg.symbol == freshLocObject) =>
        Some(Left(Fresh))
      case _ =>
        unit.error(arg.pos, "Unknown location: "+ arg +". Valid locations are parameters, local values or `this`.")
        None
    }
    
    def locList2Locality(l: List[Either[Location, AnyLoc.type]]): Locality = {
      if (l exists { case Right(_) => true }) AnyLoc
      else if (l.isEmpty) LocSet(Fresh)
      else LocSet(l map { case Left(l) => l } toSet)
    }
    
    // filter and partition `annots` into the lists below
    val (modAnn, storeAnn, assignSAnn, assignWAnn, locAnn, pureAnn) = {
      val n: List[AnnotationInfo] = Nil
      ((n, n, n, n, n, n) /: annots) {
        case ((modAnn, storeAnn, assignSAnn, assignWAnn, locAnn, pureAnn), annot) =>
          annot.atp.typeSymbol match {
            case `modClass`          => (annot :: modAnn, storeAnn, assignSAnn, assignWAnn, locAnn, pureAnn)
            case `storeClass`        => (modAnn, annot :: storeAnn, assignSAnn, assignWAnn, locAnn, pureAnn)
            case `assignStrongClass` => (modAnn, storeAnn, annot :: assignSAnn, assignWAnn, locAnn, pureAnn)
            case `assignClass`   => (modAnn, storeAnn, assignSAnn, annot :: assignWAnn, locAnn, pureAnn)
            case `locClass`          => (modAnn, storeAnn, assignSAnn, assignWAnn, annot :: locAnn, pureAnn)
            case `pureAnnotation`    => (modAnn, storeAnn, assignSAnn, assignWAnn, locAnn, annot :: pureAnn)
            case _                   => (modAnn, storeAnn, assignSAnn, assignWAnn, locAnn, pureAnn)
          }
      }
    }
    
    val store = {
      val fromMod = ((StoreLoc(): Store) /: modAnn) {
        case (store, ann) =>
          val locs = ann.args.flatMap(locationOf)
          (store /: locs)((store, loc) => loc match {
            case Right(_) => StoreAny
            case Left(loc) => store.include(loc, Fresh)
          })
      }
      
      val fromStore = ((StoreLoc(): Store) /: storeAnn) {
        case (store, ann) =>
          ann.args.flatMap(locationOf) match {
            case in :: from =>
              in match {
                case Right(_) => StoreAny
                case Left(inLoc) =>
                  val fromLoc = locList2Locality(from)
                  store.include(inLoc, fromLoc)
              }
            case _ =>
              store // there were errors reported during `locationOf`
          }
      }

      if (modAnn.isEmpty && storeAnn.isEmpty) None
      else Some(joinStore(fromMod, fromStore))
    }
    
    
    val assign = {
      def fromAss(ass: List[AnnotationInfo], useStrong: Boolean) = ((AssignLoc(): Assignment) /: ass) {
        case (assign, ann) =>
          ann.args.flatMap(locationOf) match {
            case to :: from =>
              val fromLoc = locList2Locality(from)
              to match {
                case Right(_) => AssignAny(fromLoc)
                case Left(toLoc) =>
                  assign.include(toLoc, fromLoc, useStrong)
              }
            case _ =>
              assign // again, there were errors reported during `locationOf`
          }
      }
      
      val fromStrong = fromAss(assignSAnn, true)
      val fromWeak = fromAss(assignWAnn, false)

      if (assignSAnn.isEmpty && assignWAnn.isEmpty) None
      else Some(joinAssignment(fromStrong, fromWeak))
    }
    
    val loc = {
      val res = ((LocSet(): Locality) /: locAnn) {
        case (loc, ann) =>
          val locs = ann.args.flatMap(locationOf)
          locList2Locality(locs)
      }
      
      if (locAnn.isEmpty) None
      else Some(res)
    }
    
    /**
     * Rationale: when the user puts any annotation from the "State" domain, but
     * not all of them, then he means the default for the missing ones:
     *  - "@mod()" (no modifications), if there's no annot for the "mod" domain
     *  - "@assign()" (no assignments), if there's no annot for "assign"
     *  - "@loc(any)" if there's no locality annotation
     *
     * These defaults are also used if the user puts "@pure".
     */
    
    if (store.isEmpty && assign.isEmpty && loc.isEmpty) None
    else Some((store.getOrElse(StoreLoc()), assign.getOrElse(AssignLoc()), loc.getOrElse(AnyLoc)))
  }

  def toAnnotation(elem: Elem): List[AnnotationInfo] = {
    def location2Arg(loc: Location): Tree = loc match {
      case Fresh => gen.mkAttributedRef(freshLocObject)
      case ThisLoc(sym) => gen.mkAttributedThis(sym)
      case SymLoc(sym) => gen.mkAttributedIdent(sym)
    }
    
    val anyLocArg = gen.mkAttributedRef(anyLocObject)
    
    val storeAnns = elem._1 match {
      case StoreAny =>
        List(AnnotationInfo(modClass.tpe, List(anyLocArg), Nil))
      case StoreLoc(effs) =>
        val (modOnly, others) = effs.partition(e => e._2.s.isEmpty || e._2.s.toList == List(Fresh))
        val store = {
          (for ((loc, set) <- others) yield {
            val in = location2Arg(loc)
            val from = set.s.toList.map(location2Arg)
            AnnotationInfo(storeClass.tpe, in :: from, Nil)
          }).toList
        }

        if (modOnly.isEmpty) store
        else AnnotationInfo(modClass.tpe, modOnly.map(e => location2Arg(e._1)).toList, Nil) :: store
    }
    

    val assignAnns = elem._2 match {
      case AssignAny(to) =>
        val args = anyLocArg :: (to match {
          case AnyLoc => List(anyLocArg)
          case LocSet(s) => s.toList.map(location2Arg)
        })
        List(AnnotationInfo(assignClass.tpe, args, Nil))
        
      case AssignLoc(strong, weak) =>
        def assignAnnots(annTp: Type, effs: Map[Location, Locality]) = {
          (for ((to, from) <- effs) yield {
            val args = location2Arg(to) :: (from match {
              case AnyLoc => List(anyLocArg)
              case LocSet(s) => s.toList.map(location2Arg)
            })
            AnnotationInfo(annTp, args, Nil)
          }).toList
        }
        assignAnnots(assignClass.tpe, weak) ::: assignAnnots(assignStrongClass.tpe, strong)
    }
    
    val locAnn = elem._3 match {
      case AnyLoc =>
        Nil // AnyLoc is the default when parsing the annotations
      case LocSet(s) =>
        List(AnnotationInfo(locClass.tpe, s.toList.map(location2Arg), Nil))
    }
    storeAnns ::: assignAnns ::: locAnn
  }

  override def newEffectTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(tree, typer, owner, unit)

  class StateTraverser(tree: Tree, typer: Typer, owner: Symbol, unit: CompilationUnit) extends EffectTraverser(tree, typer, owner, unit) {
    /*
    var env: i.Map[Symbol, Locality] = Map()

    protected def add(mod: State) {
      add((mod, AssignVars(), Loc()))
    }
    protected def add(ass: Assignment) {
      add((Mod(), ass, Loc()))
    }


    override def compute(): Elem = {
      val res = super.compute()
      val loc = localityOf(tree)
      res.copy(_3 = loc)
    }

    override def traverse(tree: Tree) {
      tree match {
        case ValDef(_, _, _, rhs) =>
          super.traverse(rhs)
          env = env.updated(tree.symbol, localityOf(rhs))

        case Assign(lhs, rhs) =>
          super.traverse(lhs)
          super.traverse(rhs)
          val sym = lhs.symbol

          if (env.contains(sym)) {
            env = env.updated(sym, localityOf(rhs))
          } else if (sym.owner.isMethod) {
            // assignment to some local variable
            localityOf(rhs) match {
              case NonLoc => add(AssignAll)
              case Loc(locs) =>
                add(AssignVars(Set(AssignVar(sym, locs))))
            }
          } else {
            lhs match {
              case Select(obj, field) =>
                add(new Mod(obj.symbol))
            }
          }

        case _ =>
          super.traverse(tree)
      }
    }


    /**
     * Also handle return statements (?)
     */
    def localityOf(tree: Tree): Locality = {
      NonLoc
    }

    object LocalityTraverser extends Traverser {
      import lattice.joinLocality
      private var res: Locality = Loc()

      def compute(tree: Tree) = {
        res = Loc()
        traverse(tree)
        res
      }

      override def traverse(tree: Tree) {
        tree match {
          case If(cond, thn, els) =>
            traverse(thn)
            val thnLoc = res
            traverse(els)
            res = joinLocality(res, thnLoc)
        }
      }
    } */
  }
}