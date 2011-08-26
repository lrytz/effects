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
          val (existing, others) = res.partition(aCall => sameParam(aCall.param, bCall.param))
          if (existing.isEmpty) {
            res = bCall :: others
          } else {
            val List(a) = existing
            if (a.fun.isEmpty) a :: others
            else if (a.fun == bCall.fun) a :: others
            else if (bCall.fun.isEmpty) bCall :: others
            else a :: bCall :: others
          }
        }
        PC(res)
    }
  }

  def lte(a: Elem, b: Elem): Boolean = (a, b) match {
    case (AnyPC, _) => b == AnyPC
    case (_, AnyPC) => true
    case (PC(as), PC(bs)) =>
      as.forall(aCall => {
        bs.exists(bCall => lteInfo(aCall, bCall))
      })
  }
  
  /**
   * @TODO: dok
   */
  def lteInfo(a: PCInfo, b: PCInfo) = {
    a.param == b.param && (a.fun == b.fun || b.fun.isEmpty)
  }

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

