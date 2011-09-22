package scala.tools.nsc.effects
package state

import scala.tools.nsc._
import scala.collection.{immutable => i}
import pc._

class StateChecker(val global: Global) extends EnvEffectChecker[StateLattice] with ConvertAnnots {
  import global._
  import analyzer.{Typer, Context}

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
                  Elem, toElemOps,
                  join, joinStore, joinAssignment, joinLocality,
                  mkElem}

  
  import pcLattice.{PC, PCInfo, AnyPC}

  val effectEnv = new StateEnv {
    val checker: StateChecker.this.type = StateChecker.this
  }
  import effectEnv.{Env, AnyEnv}

  override def nonAnnotatedEffect(method: Option[Symbol]): Elem = {
    def isNestedInMethod(sym: Symbol): Boolean = {
      if (sym == NoSymbol) false
      else {
        val o = sym.owner
        o.isMethod || isNestedInMethod(o)
      }
    }
    method match {
      case Some(m) if !isNestedInMethod(m) =>
        lattice.top.copy(_2 = AssignLoc())
      case _ =>
        lattice.top
    }
  }


  override def computeEffect(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) = {
    val ctx = rhsTyper.context1

    def maskStoreEffs(m: Map[Location, LocSet]) = {
      m flatMap {
        case (in, from) =>
          val inScope = from.filterOutOfScope(ctx)
          if ((in == Fresh && inScope.isFresh) || !in.isInScope(ctx)) {
            None
          } else {
            Some((in, inScope))
          }
      }
    }

    def maskAssignEffs(m: Map[SymLoc, Locality]) = {
      m flatMap {
        case (loc, to) =>
          if(loc.isInScope(ctx)) {
            Some((loc, to.filterOutOfScope(ctx)))
          } else {
            None
          }
      }
    }
    
    /* Here, we remove all @assign effects which talk about assignments of variables that are
     * out of scope. Example:
     * 
     *   def f(): Int @assign(fresh) = { var x = 1; x = 2; x }
     * 
     * The effect @assign(x, fresh) from the body is not observable outside the function.
     * 
     * @TODO: should this be done more granularly, i.e. at every place where variables can
     * get out of scope, such as the end of a Block?
     */
    val e = super.computeEffect(rhs, rhsTyper, sym, unit)
    val maskedStore = e._1 match {
      case sa @ StoreAny => sa
      case StoreLoc(effs) =>
        val effs1 = maskStoreEffs(effs)
        StoreLoc(effs1)
    }
    val maskedAssign = e._2 match {
      case aa @ AssignAny(_) => aa
      case AssignLoc(effs) =>
        val effs1 = maskAssignEffs(effs)
        AssignLoc(effs1)
    }
    val maskedLoc = e._3.filterOutOfScope(ctx)

    val res = (maskedStore, maskedAssign, maskedLoc)
    if (res != e) { println("masking effecs:\n  from: "+ e +"\n  to  : "+ res) } // @DEBUG
    res
  }
  
  /**
   * @TODO: override computePrimConstrEffect to do masking, similar to computeEffect above.
   */
  
  override def newEnvEffectTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(rhs, env, rhsTyper, sym, unit)


  class StateTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends EnvEffectTraverser(rhs, env, rhsTyper, sym, unit) {
    override def traverse(tree: Tree) {
      tree match {
        
        case Block(stats, expr) =>
          val statsRes = seq(env, stats: _*)
          val exprRes = analyze(statsRes.env, expr)
          val eff = (statsRes.eff u exprRes.eff).updateLocality(exprRes.eff._3)
          add(eff)

        case If(cond, thenExpr, elseExpr) =>
          val condRes = analyze(env, cond)
          val thenElseRes = or(condRes.env, thenExpr, elseExpr)
          val eff = (condRes.eff u thenElseRes.eff).updateLocality(thenElseRes.eff._3) 
          add(eff)

        case Try(block, catches, finalizer) =>
          val blockRes = analyze(env, block)
          // @TODO: catches. the patterns happen in sequence, but the pattern bodies we can treat as `or`, as only one of them gets executed.
          val finRes = analyze(blockRes.env, finalizer)
          add(blockRes.eff u finRes.eff) // @TODO: resulting locality is a merge of block and catches (but not the finalizer, that's executed as a statement)

        // Apply, TypeApply: handled ok in superclass (EffectTraverser, call to handleApplication)

        case Select(qual, name) =>
          val sym = tree.symbol
          if (sym.isMethod) {
            // applications to parameterless methods are `Select` trees, e.g. getters
            handleApplication(tree)
          } else {
            // selection of an object or a field (inside a setter, fields are selected)
            val qualEff = subtreeEffect(qual, env)
            val qualEnv = env.applyEffect(qualEff)
            
            val loc = {
              if (sym.owner.isClass) { // it's a field
                if (sym.hasAnnotation(localClass))
                  qualEff._3
                else
                  AnyLoc
              } else {
                selectedLocality(sym, qualEnv, rhsTyper.context1)
              }
            }
            add((qualEff._1, qualEff._2, loc))
          }

        case Ident(name) =>
          val sym = tree.symbol
          if (sym.isMethod) {
            handleApplication(tree)
          } else {
            // an Ident tree can refer to parameters, local values or packages in the `root` package.
            // in the last case, selectedLocality returns AnyLoc
            add(mkElem(selectedLocality(sym, env, rhsTyper.context1)))
          }

        case Assign(lhs, rhs) =>
          val lhsRes = analyze(env, lhs)
          val rhsRes = analyze(lhsRes.env, rhs)
          val rhsLoc = rhsRes.eff._3

          val lhsSym = lhs.symbol
          val owner = lhsSym.owner
     
          val assignmentEffect = if (owner.isClass) {
            // if the lefthand side is a selection of a field, then the assignment has a `@store` effect
            if (owner.isModuleClass) mkElem(StoreAny)
            else {
              // we can assume that we're assigning a field of `this`. all other assignments go through the setter.
              val loc = ThisLoc(owner)
              if (lhsSym.hasAnnotation(localClass)) {
                rhsLoc match {
                  case AnyLoc => mkElem(StoreAny)
                  case from @ LocSet(_) => mkElem(StoreLoc(loc, from))
                }
              } else {
                // assign to a non-local field (c.x) has the effect @mod(c)
                mkElem(StoreLoc(loc, LocSet(Fresh)))
              }
            }
          } else {
            // it's an assignment to a local variable (not a field), therefore an `@assign` effect
            mkElem(AssignLoc(SymLoc(lhsSym), rhsLoc))
          }

          val resEff = lhsRes.eff u rhsRes.eff u assignmentEffect
          add(resEff.updateLocality(LocSet())) // no value is returned, so there's no locality

        case ValDef(mods, name, tpt, rhs) =>
          val sym = tree.symbol
          val rhsEffect = subtreeEffect(rhs, env)
          val rhsLoc = rhsEffect._3
          val res = if (sym.isLocal) {
            // the assign effect will be used to set the environment correctly
            val assignEffect = mkElem(AssignLoc(SymLoc(sym), rhsLoc))
            rhsEffect u assignEffect
          } else {
            // it's a field definition (in the body of a template, while `computePrimaryConstrEff`)
            // so, compute the effect of the field initialization
            if (sym.owner.isModuleClass) {
              rhsEffect u mkElem(StoreAny)
            } else {
              if (sym.hasAnnotation(localClass)) rhsLoc match {
                case l if l.isFresh =>
                  val loc = ThisLoc(sym.owner)
                  val storeEff = mkElem(StoreLoc(loc, LocSet(Fresh)))
                  rhsEffect u storeEff
                case _ =>
                  rhsEffect u mkElem(StoreAny) // @TODO: why always StoreAny, not a store effect to the location (if it's a SymLoc)???
              } else {
                val storeEff = mkElem(StoreLoc(ThisLoc(sym.owner), LocSet(Fresh)))
                rhsEffect u storeEff
              }
            }
          }
          add(res.updateLocality(LocSet()))

        case New(tpt) =>
          // no side effects - the constructor call is represented as a separate Apply tree
          add(mkElem(LocSet(Fresh)))
        
        case Super(qual, mix) =>
          add(mkElem(LocSet(ThisLoc(tree.symbol))))

        case This(qual) =>
          add(mkElem(LocSet(ThisLoc(tree.symbol))))

        case Literal(c) =>
          add(mkElem(LocSet(Fresh)))
          
        // @TODO: LabelDef!!! while and do-while loops are expressed with Labels.

        case _ =>
          super.traverse(tree)
      }
        
    }
    
    override def handleApplication(tree: Tree) {
      val (fun, targs, argss) = decomposeApply(tree)
      val funSym = fun.symbol
      val ctx = rhsTyper.context1
      
      val funRes = qualEffect(fun, env)
      val qualLoc = funRes.eff._3
      
      val targsRes = seq(funRes.env, targs: _*)

      // cannot use `seq` because we need the intermediate results (locations of all args)
      val argssRes = seq(targsRes.env, argss.flatten: _*)
      val flatArgLocs = argssRes.parts.map(_._3)
      
      // build a map from the function's parameter symbols to the localities of the arguments
      val paramsMap: Map[Location, Locality] = {
        // For methods in classes (not objects), modifications to `this` mean modifications to the receiver (funLoc)
        val receiverMap = if (funSym.owner.isModuleClass) Map() else Map(ThisLoc(funSym.owner) -> qualLoc)
        val flatParams = funSym.tpe.paramss.flatten
        receiverMap ++ ((flatParams map SymLoc) zip flatArgLocs)
      }

      val (latentEff, pcEffs) = computeApplicationEffect(fun, targs, argss, rhsTyper.context1)
      val mappedLatent = mapLocalities(latentEff, argssRes.env, paramsMap)
      val mappedPcs = pcEffs.map(e => mapPcLocalities(e._1, e._2, argssRes.env, paramsMap))
      
      val appEff = if (pcEffs.isEmpty) {
        mappedLatent
      } else {
        combineLatentPc(mappedLatent, mappedPcs, argssRes.env)
      }
      
      val totalEff = funRes.eff u targsRes.eff u argssRes.eff u appEff
      add(totalEff.updateLocality(appEff._3))
    }
  }
  
  
  /**
   * During a function application, combine a latent effect and effects
   * obtained through polymorphism.
   * 
   * We don't know in which order these effects happen in the applied
   * method. Therefore we need to assume worst-case. We apply all effects
   * to the environment, and then re-map the locations in the effects
   * using that generalized environment. This is done until reaching
   * a fixpoint.
   */
  def combineLatentPc(latent: Elem, pcs: List[Elem], env: Env): Elem = {
    var prevEnv = env
    var prevEff = (latent :: pcs).reduceRight(_ u _)

    var resEnv = env.applyEffect(latent)
    for (pc <- pcs) resEnv = resEnv.applyEffect(pc)
    var resLatent = applyEnv(latent, resEnv)
    var resPcs = pcs.map(applyEnv(_, resEnv))
    var resEff = (resLatent :: resPcs).reduceRight(_ u _)

    while(!(resEff <= prevEff)) {
      prevEnv = resEnv
      prevEff = resEff
      
      resEnv = resEnv.applyEffect(resLatent)
      for (pc <- resPcs) resEnv = resEnv.applyEffect(pc)
      resLatent = applyEnv(resLatent, resEnv)
      resPcs = resPcs.map(applyEnv(_, resEnv))
      resEff = (resLatent :: resPcs).reduceRight(_ u _)
    }
    resEff
  }

  /**
   * Map the locations in `eff` using `env` and the `paramsMap`. For example, in
   *   
   *   class A { def mod(): Unit @mod(this) }
   *   def f(a: A) = { a.mod() }
   * 
   * the effect of the application `a.mod()` is transformed into `@mod(a)`.
   * 
   * The env is applied first. This is because the target locations in the `paramsMap` are
   * already according to the current env, and therefore they don't need to be mapped over
   * `env` again.
   */
  def mapLocalities(eff: Elem, env: Env, paramsMap: Map[Location, Locality]) = {
    applyParamsMap(applyEnv(eff, env), paramsMap)
  }

  def mapPcLocalities(pcEff: Elem, pcInfo: PCInfo, env: Env, paramsMap: Map[Location, Locality]) = {
    /* Example: consider we treat the application of method `foo`, e.g.
     * 
     *   qual.foo(arg)
     * 
     * where
     *
     *   def foo(a: A) @pc(a.bar(_))
     *   class A { def bar(b: B) @mod(this) @mod(b) }
     * 
     * Then the arguments to `mapPcLocalities` are
     *   pcEff  = @mod(this) @mod(b)
     *   pcInfo = PCInfo(a, bar)
     *
     * The correct locality map to apply is the following:
     * 
     *   this -> { localityOf(arg) }
     *   b    -> AnyLoc
     * 
     * For recursively found PC calls (e.g. there's "@pc(b.baz)" on bar), the
     * parameter location ("b") won't be found in the current environemnt and
     * will be mapped to AnyLoc.
     */
    val paramLoc = pcInfo.param match {
      case pcLattice.ThisLoc(c) =>
        ThisLoc(c)
      case pcLattice.ParamLoc(p) =>
        SymLoc(p)
    }

    val pcMap: Map[Location, Locality] = pcInfo.fun match {
      case Some(fun) =>
        val thisLocality = paramsMap.getOrElse(paramLoc, AnyLoc) // currentEnv.lookup(paramLoc).getOrElse(AnyLoc)
        Map(ThisLoc(fun.owner) -> thisLocality) ++ (fun.paramss.flatten.map(p => SymLoc(p) -> AnyLoc))
      case None =>
        abort("no function defined for pc call: "+ pcEff +", "+ pcInfo)
    }
    
    mapLocalities(pcEff, env, pcMap)
  }

  /**
   * Map the locations in `eff` according to `env`.
   */
  def applyEnv(eff: Elem, env: Env): Elem = {
    applyLocationTransform(eff, env.lookup(_))
  }
  
  /**
   * Map the locations in `eff` according to `paramsMap`.
   */
  def applyParamsMap(eff: Elem, paramsMap: Map[Location, Locality]): Elem = {
    applyLocationTransform(eff, loc => paramsMap.getOrElse(loc, LocSet(loc)))
  }
  
  def applyLocationTransform(eff: Elem, trans: Location => Locality) = {
    val store = eff._1 match {
      case StoreAny => StoreAny
      case StoreLoc(effs) =>
        ((StoreLoc(): Store) /: effs) {
          case (store, (in, from)) =>
            val mappedFrom = mapLocality(from, trans)
            var res = store
            trans(in) match {
              case AnyLoc =>
                res = StoreAny
              case LocSet(locs) =>
                for (loc <- locs) { res = res.include(loc, mappedFrom) }
            }
            res
        }
    }

    val assign = eff._2 match {
      case AssignAny(to) => AssignAny(mapLocality(to, trans))
      case AssignLoc(effs) =>
        val mapEffs = effs.map(e => (e._1, mapLocality(e._2, trans)))
        AssignLoc(mapEffs)
    }
    
    val loc = mapLocality(eff._3, trans)
    (store, assign, loc)

  }
  
  def mapLocality(loc: Locality, trans: Location => Locality) = loc match {
    case AnyLoc => AnyLoc
    case LocSet(locs) =>
      ((LocSet(): Locality) /: locs)((set, loc) => joinLocality(set, trans(loc)))
  }
  

  /**
   * Check if the owner chain of `sym` contains `owner`.
   */
  def hasOwner(sym: Symbol, owner: Symbol): Boolean = {
    if (sym == NoSymbol) false
    else if (sym.owner == owner) true
    else hasOwner(sym.owner, owner)
  }
  
  /**
   * Is the symbol `sym` defined in an enclosing method?
   * For each enclosing method, we check if the symbol is defined in it.
   */
  def definedInEnclMethod(sym: Symbol, rhsCtx: Context): Boolean = {
    if (rhsCtx.outer == rhsCtx) false
    else hasOwner(sym, rhsCtx.owner) || definedInEnclMethod(sym, rhsCtx.enclMethod)
  }
  
  /**
   * The locality of a selected symbol, i.e. the locality of a Select or Ident tree.
   * 
   *  - if the symbol is a parameter or a local value / variable defined in the current
   *    or an outer method, then look up the locality in the environment
   *
   *  - if the symbol is anything else, AnyLoc
   */
  def selectedLocality(sym: Symbol, env: Env, ctx: Context): Locality = {
    val res = if((sym.isParameter || sym.isLocal) && definedInEnclMethod(sym, ctx)) {
      env.lookup(SymLoc(sym))
    } else {
      AnyLoc
    }
    println("locality of selected "+ sym +" is "+ res) // @DEBUG
    res
  }
}
