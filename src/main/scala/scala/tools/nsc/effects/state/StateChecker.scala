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
  import effectEnv.{Env, EnvMap, AnyEnv}

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
    val ctx = rhsTyper.context1.outer
    def onlyInScope(m: Map[Location, Locality]) = {
      m.filter {
        case (SymLoc(sym), to) =>
          assert(sym.isLocal, sym)
          localIsInScope(sym, ctx)
        case _ =>
          true
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
     * get out of scope, such as the end of a Block? Does it matter to keep them until the
     * 
     * Note that we don't need to do anything similar for state modificaiton effects. The
     * locations used in @state effects are never local variables that can get out of scope.
     * Instead, @state effects only refer to parameters or `this`, and these don't get out
     * of scope.
     * 
     * However, we remove effects of the form @mod(fresh), since they're equivalent to but
     * more verbose than @mod().
     */
    val e = super.computeEffect(rhs, rhsTyper, sym, unit)
    val maskedStore = e._1 match {
      case sa @ StoreAny => sa
      case StoreLoc(effs) =>
        StoreLoc(effs.filterNot {
          case (Fresh, v) => v.isFresh
          case _ => false
        })
    }
    val maskedAssign = e._2 match {
      case aa @ AssignAny(_) => aa
      case AssignLoc(effs) =>
        val effs1 = onlyInScope(effs)
        AssignLoc(effs1)
    }
    val res = e.copy(_1 = maskedStore, _2 = maskedAssign)
    if (res != e) { println("masking assign effect to out-of-scope variables:\n  from: "+ e +"\n  to  : "+ res) } // @DEBUG
    res
  }
  
  /**
   * @TODO: override computePrimConstrEffect to do masking, as in computeEffect above?
   */
  
  override def newEnvEffectTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(rhs, env, rhsTyper, sym, unit)


  class StateTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends EnvEffectTraverser(rhs, env, rhsTyper, sym, unit) {
    override def traverse(tree: Tree) {
      tree match {
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
            if (sym.owner.isRootPackage) add(mkElem(AnyLoc)) // @TODO: should `root` package be handled in `selectedLocality`?
            else add(mkElem(selectedLocality(sym, env, rhsTyper.context1)))
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
      val funLoc = funRes.eff._3 // @TODO: this only works "by chance", because we use "qualEffect", which actually returns the locality of the function's qualifier. maybe just rename "funLoc" to "qualLoc" to make things clear.
      
      val targsRes = seq(funRes.env, targs: _*)

      // foldRight traverses left to right (that's the order in which
      // effects happen, the order of evaluation for the arguments).
      val (argssRes, flatArgLocs) = (((lattice.bottom, targsRes.env), List[Locality]()) /: argss.flatten) {
        case (((eff, env), locs), arg) =>
          val res = analyze(env, arg)
          ((eff u res.eff, res.env), res.eff._3 :: locs)
      }

      
      def applicationEnv(localEnv: Env): Env = {
        // build a map from the function's parameter symbols to the localities of the arguments
        val paramsMap: Map[Location, Locality] = {
          // For methods in classes (not objects), modifications to `this` mean modifications to the receiver (funLoc)
          val receiverMap = if (funSym.owner.isModuleClass) Map() else Map(ThisLoc(funSym.owner) -> funLoc)
          val flatParams = funSym.tpe.paramss.flatten
          receiverMap ++ ((flatParams map SymLoc) zip flatArgLocs)
        }
      
        /* The environment that is used for adapting the application effect, see adaptLatentEffect.
         * It's important to start from the current environment, because the effect annotations of
         * the applied function might refer to params / locals of the current method, which have a
         * specific locality in the current environment. Example
         * 
         * def f(a: A) {
         *   var x = a
         *   def g(): Unit @mod(x) = { x.modify() }
         *   g()
         * }
         * 
         * When applying `g`, the latent effect is `@mod(x)`, which at this point of the program
         * has to be mapped to `@mod(a)`.
         */
        localEnv.mapLocations(paramsMap)
      }
      
      def adaptEffs(latent: Elem, pcs: List[(Elem, PCInfo)]): Elem = {
        val lat = adaptLatentEffect(latent, fun, targs, argss, ctx)
        var res = lat
        for ((pcEff, pcInfo) <- pcs)
          res = res u adaptPcEffect(pcEff, pcInfo, ctx)
        res.updateLocality(lat._3)
      }

      
      val (latentEff, pcEffs) = computeApplicationEffect(fun, targs, argss, rhsTyper.context1)
      
      
      val appEff = if (pcEffs.isEmpty) {
        withEnv(applicationEnv(argssRes.env)) { adaptLatentEffect(latentEff, fun, targs, argss, ctx) }
      } else {
        var prevRes = withEnv(applicationEnv(argssRes.env)) { adaptEffs(latentEff, pcEffs) }
        var appEnv = argssRes.env.applyEffect(prevRes)
        var res = withEnv(applicationEnv(appEnv)) { adaptEffs(latentEff, pcEffs) }
        while (!(res <= prevRes)) {
          prevRes = res
          appEnv = appEnv.applyEffect(prevRes)
          res = withEnv(applicationEnv(appEnv)) { adaptEffs(latentEff, pcEffs) }
        }
        res
      }
      
      val totalEff = funRes.eff u targsRes.eff u argssRes.eff u appEff
      add(totalEff.updateLocality(appEff._3))
    }
  }
  
  override def adaptLatentEffect(eff: Elem, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
    mapLocalities(eff, currentEnv, ctx)
    
    /* @TODO first thought: this is not enough!!!
     *
     * If there are multiple assign / modification effects in `eff`, then these need to be
     * combined, the localities must be merged until reaching a fixpoint. For example
     * 
     *   def foo(a: A, b: B) = {
     *     a.store(b)
     *     b.modify()
     *   }
     * 
     * second thought: really???
     * (=> continue example: local environment that is modified by the two effects. does it always stay well-formed?)
     */
    
  }

  override def adaptPcEffect(eff: Elem, pc: PCInfo, ctx: Context): Elem = {
    /* Example: consider we treat the application of method `foo`, e.g.
     * 
     *   qual.foo(arg)
     * 
     * where
     *
     *   def foo(a: A) @pc(a.bar(_))
     *   class A { def bar(b: B) @mod(this) @mod(b) }
     * 
     * Then the arguments to `adaptPcEffect` are
     *   eff   = @mod(this) @mod(b)
     *   pc    = PCInfo(a, bar)
     * 
     * We have to map the localities of `@mod(this) @mod(b)` according to the
     * current environment (in which "a" is mapped to "localityOf(arg)").
     * The correct locality map to apply is the following:
     * 
     *   this -> { localityOf(arg) }
     *   b    -> AnyLoc
     * 
     * For recursively found PC calls (e.g. there's "@pc(b.baz)" on bar), the
     * parameter location ("b") won't be found in the current environemnt and
     * will be mapped to AnyLoc.
     */
    val paramLoc = pc.param match {
      case pcLattice.ThisLoc(c) =>
        ThisLoc(c)
      case pcLattice.ParamLoc(p) =>
        SymLoc(p)
    }
    // @TODO: fix when enabling PC calls on `this`

    val pcEnv = pc.fun match {
      case None => AnyEnv
      case Some(fun) =>
        val thisLocality = currentEnv.lookup(paramLoc).getOrElse(AnyLoc)
        val map: Map[Location, Locality] = Map(ThisLoc(fun.owner) -> thisLocality) ++ (fun.paramss.flatten.map(p => SymLoc(p) -> AnyLoc))
        currentEnv.mapLocations(map)
    }
    mapLocalities(eff, pcEnv, ctx)
  }

  /**
   * Map the locations mentioned in `eff` according to the environment `env` and
   * the context `ctx`. This method is used in method applications for adapting
   * the locations of state effects. For example, in
   *   
   *   class A { def mod(): Unit @mod(this) }
   *   def f(a: A) = { a.mod() }
   * 
   * the effect of the application `a.mod()` is transformed into `@mod(a)`.
   */
  def mapLocalities(eff: Elem, env: Env, ctx: Context) = {
    val store = eff._1 match {
      case StoreAny => StoreAny
      case StoreLoc(effs) =>
        ((StoreLoc(): Store) /: effs) {
          case (store, (in, from)) =>
            val mappedFrom = mapLocality(from, env, ctx)
            var res = store
            localityOf(in, env, ctx) match {
              case AnyLoc =>
                res = StoreAny
              case LocSet(locs) =>
                for (loc <- locs) { res = res.include(loc, mappedFrom) }
            }
            res
        }
    }
    
    val assign = eff._2 match {
      case AssignAny(to) => AssignAny(mapLocality(to, env, ctx))
      case AssignLoc(effs) =>
        val mapEffs = effs.map(e => (e._1, mapLocality(e._2, env, ctx)))
        AssignLoc(mapEffs)
    }
    
    val loc = mapLocality(eff._3, env, ctx)
      
    (store, assign, loc)
  }
    
  def mapLocality(loc: Locality, env: Env, ctx: Context) = loc match {
    case AnyLoc => AnyLoc
    case LocSet(locs) =>
      ((LocSet(): Locality) /: locs)((set, loc) => joinLocality(set, localityOf(loc, env, ctx) /* map.getOrElse(loc, nonMappedLocality(loc, ctx))*/))
  }
  
  /**
   * Is the local value / variable or paramter `local` in scope with
   * respect to context `ctx`?
   *
   * This is checked by looking at the owner of `ctx` and all owner
   * symbols of its `outer` contexts. If any of these symbols is the
   * same as the owner of `local`, then that local value is in scope
   * with respect to that context.
   * 
   * Note that this only works correctly for local values / variables
   * and parameters. Inherited fields can be in scope while only a
   * subclass is in the context chain, not the actual owner of the field.
   */
  def localIsInScope(local: Symbol, ctx: Context): Boolean = {
    def contextHasOwner(ctx: Context, owner: Symbol): Boolean = {
      ctx.owner == owner || (ctx.outer != ctx && contextHasOwner(ctx.outer, owner))
    }
    contextHasOwner(ctx, local.owner)
  }

  /**
   * Is the local value / variable or parameter `local` defined in the
   * context `ctx`?
   *
   * Assumes that the symbol `local` is in scope with respect to `ctx`.
   */
  def definedInCurrentMethod(local: Symbol, ctx: Context): Boolean = {
    !localIsInScope(local, ctx.outer)
  }
  
  
  /**
   * The locality of a selected symbol, i.e. the locality of a Select or Ident tree.
   * 
   *  - if the symbol is a parameter of the current method, or a local value / variable
   *    defined in the current method, then look up the locality in the environment
   *
   *  - if the symbol is a parameter of an outer method, or a local value / variable
   *    defined in an outer method, SymLoc(sym)
   *
   *  - if the symbol is anything else, AnyLoc
   */
  def selectedLocality(sym: Symbol, env: Env, ctx: Context): Locality = {
    val loc = SymLoc(sym)
    val res = if(sym.isParameter || sym.isLocal) {
      assert(localIsInScope(sym, ctx), "local not in scope: "+ sym)
      if (definedInCurrentMethod(sym, ctx)) {
        env.lookup(loc).getOrElse({
          // the default location of a local symbol defined in the current method.
          if (sym.isParameter) LocSet(loc)
          else LocSet(Fresh)
        })
      } else {
        // it's a local value / param from an outer method.
        LocSet(loc)
      }
    } else {
      AnyLoc
    }
    println("locality of selected "+ sym +" is "+ res) // @DEBUG
    res
  }
  
  /**
   * The locality of a location, considering the current environemnt `env` and the
   * current context `ctx`.
   * 
   * This method is used by `mapLocalities` (i.e. `mapLocality`), see its documentation.
   *
   * It works similarly to the method `selectedLocality` above, see its documentation.
   */
  def localityOf(loc: Location, env: Env, ctx: Context): Locality = loc match {
    case SymLoc(sym) =>
      assert(sym.isParameter || sym.isLocal)
      val res = if (localIsInScope(sym, ctx)) {
        selectedLocality(sym, env, ctx)
      } else {
        env.lookup(loc).getOrElse(AnyLoc)
      }
      println("locality of mapped "+ sym +" is "+ res) // @DEBUG
      res

    case ThisLoc(_) =>
      /* @TODO: what's a good default? basically, the default should never happen
       * to be used. When looking up the locality of a ThisLoc, it can only be
       * during `adaptLatentEffect` or `adaptPcEffect`, and then the `ThisLoc`
       * should be present.
       */
      env.lookup(loc).getOrElse(AnyLoc)

    case Fresh =>
      // @TODO: can this case ever arise? 
      LocSet(Fresh)
  }
}
