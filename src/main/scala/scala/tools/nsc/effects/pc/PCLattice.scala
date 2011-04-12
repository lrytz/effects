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
          val (existing, other) = res.partition(aCall => aCall.param == bCall.param && aCall.fun == bCall.fun)
          if (existing.isEmpty) {
            res = bCall :: other
          } else {
            res = PCInfo(bCall.param, bCall.fun, combine(bCall.argtpss, existing.head.argtpss)) :: other
          }
        }
        PC(res)
    }
  }

  private def combine(tss1: List[List[Type]], tss2: List[List[Type]]): List[List[Type]] = {
    (tss1, tss2).zipped.map((ts1, ts2) =>
      (ts1, ts2).zipped.map((t1, t2) =>
        lub(List(t1, t2))
      )
    )
  }

  def lte(a: Elem, b: Elem): Boolean = (a, b) match {
    case (AnyPC, _) => b == AnyPC
    case (_, AnyPC) => true
    case (PC(as), PC(bs)) =>
      as.forall(aCall => {
        bs.exists(bCall => bCall.fun == aCall.fun) // @TODO: check paramtpss
      })
  }

  sealed case class PCInfo(param: Symbol, fun: Symbol, argtpss: List[List[Type]])
  object PCInfo {
    implicit def singlePC(info: PCInfo): PC = PC(List(info))
  }
  sealed trait PCElem
  case class PC(pcs: List[PCInfo]) extends PCElem
  case object AnyPC extends PCElem
  
}

