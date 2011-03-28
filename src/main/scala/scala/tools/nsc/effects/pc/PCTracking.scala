package scala.tools.nsc.effects
package pc

trait PCTracking[L <: CompleteLattice] { this: EffectChecker[L] =>
  import global._
  import analyzer.Context

  val pcCommons = new PCCommons {
    val global: PCTracking.this.global.type = PCTracking.this.global
  }
  import pcCommons._
  import pcLattice.{PC, PCInfo, AnyPC}


    /*
   * @paramCall(a.bar(~: String))
   * def foo(a: A) { a.bar(s) }
   *
   * x.y.foo(new B)
   *
   *  - fun: "x.y.foo"                 tree
   *  - targs: Nil                     trees
   *  - argss: List(List("a"))         trees
   *
   *  - pcparam: a                     symbol
   *  - pcfun: A.bar                   symbol
   *  - pcargtpss: List(List(String))  types
   *
   * need to find out which of the "argss" corresponds to "pcparam"
   *
   */

  addAppEffectTransformer((e: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) => {
    var res = e

    val flatArgss = argss.flatten
    val flatParamss = fun.symbol.tpe.paramss.flatten

    val annots = fun.symbol.tpe.finalResultType.annotations
    pcFromAnnotations(annots) match {
      case None | Some(AnyPC) =>
        res = lattice.join(res, anyParamCall(flatArgss, ctx))
      case Some(PC(calls)) =>
        for (PCInfo(param, pcfun, pcargtpss) <- calls) {
          val i = flatParamss.indexOf(param)
          assert(i >= 0)
          flatArgss(i) match {
            case id @ Ident(_) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
              ()
            case arg =>
              // @TODO: overloads.. there should be a more symbolic way to do this. asSeenFrom?
              val sym = arg.tpe.member(pcfun.name)
              res = lattice.join(e, fromAnnotation(sym.tpe).getOrElse(lattice.top))
          }
        }
    }
    res
  })

  // @TODO: effect of calling all methods on all types of `args`
  def anyParamCall(args: List[Tree], ctx: Context): Elem =
    (lattice.bottom /: args)((res, arg) => {
      arg match {
        case id @ Ident(_) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
          res
        case _ =>
          lattice.top
      }
    })


  /**
   * Detect param calls: they don't have any effect!
   */
  addAppEffectTransformer((e: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context) => {
    fun match {
      case Select(id @ Ident(_), _) if (isParam(id.symbol, ctx.owner.enclMethod)) =>
        lattice.bottom

      case _ =>
        e
    }
  })
}
