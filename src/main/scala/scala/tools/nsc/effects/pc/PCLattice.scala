package scala.tools.nsc.effects
package pc

import scala.tools.nsc._

abstract class PCLattice extends CompleteLattice {
  val global: Global
  import global._

  type Elem = PCElem

  val bottom = PC(Nil)
  val top    = AnyPC

  def join(a: Elem, b: Elem): Elem = {
    (a, b) match {
      case (AnyPC, _) | (_, AnyPC) =>
        AnyPC
        
      case (PC(as), PC(bs)) =>
        var res = as
        for (bCall <- bs) {
          
          // include `bCall` into `res`. First find `existing` paramCalls in res that have the same param
          
          val (existing, others) = res.partition(aCall => sameParam(aCall.param, bCall.param))
          if (existing.isEmpty) {
            res = bCall :: others
          } else {
            existing.find(_.fun.isEmpty) match {
              case Some(a) =>
                // if there's an existing paramCall which covers all methods, take only that.
                a :: others
              case None =>
                // if b covers all methods, take only b, drop the existing
                if (bCall.fun.isEmpty) bCall :: others
                // otherwise, if the same paramCall already exists, drop b
                else if (existing.exists(_.fun == bCall.fun)) res
                // otherwise, include b
                else bCall :: res
            }
          }
        }
        PC(res)
    }
  }

  def lte(a: Elem, b: Elem): Boolean = (a, b) match {
    case (_, AnyPC) => true
    case (AnyPC, _) => false
    case (PC(as), PC(bs)) =>
      as.forall(aCall => {
        bs.exists(bCall => lteInfo(aCall, bCall))
      })
  }

  /**
   * Test if the PCInfo a is smaller or equal to b.
   *  - the params have to be the same
   *  - the functions have to be the same, or b covers all functions
   */
  def lteInfo(a: PCInfo, b: PCInfo) = {
    sameParam(a.param, b.param) && (a.fun == b.fun || b.fun.isEmpty)
  }

  /**
   * Represents one parameter call annotation. If `fun` is None, the
   * parameter call covers all methods on `param`, i.e. an annotation
   * of the form
   *   def f(a: A): R @pc(a)
   */
  sealed case class PCInfo(param: Symbol, fun: Option[Symbol])

  sealed trait PCElem
  case class PC(pcs: List[PCInfo]) extends PCElem
  case object AnyPC extends PCElem

  /**
   * True if `a` and `b` denote the same parameter.
   * 
   * We cannot just compare the symbols for equality. The reason is that there might be
   * multiple symbols for the same parameter, the one in the MethodType can be different
   * than the one assigned to trees. (When cloning a MethodType, new parameter symbols
   * get created). Therefore, we commpare owner (the method) and name.
   */
  def sameParam(a: Symbol, b: Symbol) = a.owner == b.owner && a.name == b.name
}

