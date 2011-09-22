package scala.tools.nsc.effects
package state

import scala.tools.nsc._

trait ConvertAnnots { this: StateChecker =>
  import global._
  import lattice.{Locality, AnyLoc, LocSet,
                  Location, SymLoc, Fresh, ThisLoc,
                  Store, StoreAny, StoreLoc,
                  Assignment, AssignAny, AssignLoc,
                  Elem,
                  join, joinStore, joinAssignment, joinLocality}

  /* Annotation Classes */
  val modClass = definitions.getClass("scala.annotation.effects.state.mod")
  val storeClass = definitions.getClass("scala.annotation.effects.state.store")
  val assignClass = definitions.getClass("scala.annotation.effects.state.assign")
  val locClass = definitions.getClass("scala.annotation.effects.state.loc")

  val localClass = definitions.getClass("scala.annotation.effects.state.local")

  val annotationClasses = List(modClass, storeClass, assignClass, locClass)

  
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
      if (l.exists(_.isRight)) AnyLoc
      else if (l.isEmpty) LocSet(Fresh)
      else LocSet(l map { case Left(l) => l } toSet)
    }
    
    // filter and partition `annots` into the lists below
    val (modAnn, storeAnn, assignAnn, locAnn, pureAnn) = {
      val n: List[AnnotationInfo] = Nil
      ((n, n, n, n, n) /: annots) {
        case ((modAnn, storeAnn, assignAnn, locAnn, pureAnn), annot) =>
          annot.atp.typeSymbol match {
            case `modClass`          => (annot :: modAnn, storeAnn, assignAnn, locAnn, pureAnn)
            case `storeClass`        => (modAnn, annot :: storeAnn, assignAnn, locAnn, pureAnn)
            case `assignClass`       => (modAnn, storeAnn, annot :: assignAnn, locAnn, pureAnn)
            case `locClass`          => (modAnn, storeAnn, assignAnn, annot :: locAnn, pureAnn)
            case `pureAnnotation`    => (modAnn, storeAnn, assignAnn, locAnn, annot :: pureAnn)
            case _                   => (modAnn, storeAnn, assignAnn, locAnn, pureAnn)
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
      def fromAss(ass: List[AnnotationInfo]) = ((AssignLoc(): Assignment) /: ass) {
        case (assign, ann) =>
          ann.args.flatMap(locationOf) match {
            case to :: from =>
              val fromLoc = locList2Locality(from)
              to match {
                case Right(_) => AssignAny(fromLoc)
                case Left(toLoc @ SymLoc(_)) =>
                  assign.include(toLoc, fromLoc)
                case _ =>
                  unit.error(ann.pos, "@assign effect to a non-variable: "+ to)
                  assign
              }
            case _ =>
              assign // again, there were errors reported during `locationOf`
          }
      }
      
      val fromAnn = fromAss(assignAnn)

      if (assignAnn.isEmpty) None
      else Some(fromAnn)
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
    
    if (store.isEmpty && assign.isEmpty && loc.isEmpty && pureAnn.isEmpty) None
    else Some((store.getOrElse(StoreLoc()), assign.getOrElse(AssignLoc()), loc.getOrElse(AnyLoc)))
  }


  def toAnnotation(elem: Elem): List[AnnotationInfo] = {
    def location2Arg(loc: Location): Tree = loc match {
      case Fresh => gen.mkAttributedRef(freshLocObject)
      case ThisLoc(sym) => gen.mkAttributedThis(sym)
      case SymLoc(sym) => gen.mkAttributedIdent(sym)
    }
    
    /* @TODO: this is already wrong, it yields a tree which pretty-prints as
     *   state.this.any
     *
     *   Select(This(state), "any")
     *
     * where `state` is symbol of package `state`.
     */
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
        
      case AssignLoc(effs) =>
        def assignAnnots(annTp: Type, effs: Map[SymLoc, Locality]) = {
          (for ((to, from) <- effs) yield {
            val args = location2Arg(to) :: (from match {
              case AnyLoc => List(anyLocArg)
              case LocSet(s) => s.toList.map(location2Arg)
            })
            AnnotationInfo(annTp, args, Nil)
          }).toList
        }
        assignAnnots(assignClass.tpe, effs)
    }
    
    val locAnn = elem._3 match {
      case AnyLoc =>
        Nil // AnyLoc is the default when parsing the annotations
      case LocSet(s) =>
        List(AnnotationInfo(locClass.tpe, s.toList.map(location2Arg), Nil))
    }
    val res = storeAnns ::: assignAnns ::: locAnn
    // if all three parts of the effect happen to be the default, we still need an annotation
    // to indicate that. so we just put @mod()
    if (res.isEmpty)
      List(AnnotationInfo(modClass.tpe, Nil, Nil))
    else
      res
  }
}