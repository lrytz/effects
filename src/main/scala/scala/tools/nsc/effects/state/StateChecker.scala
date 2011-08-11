package scala.tools.nsc.effects
package state

import scala.tools.nsc._
import scala.collection.{immutable => i}
import pc._

class StateChecker(val global: Global) extends EffectChecker[StateLattice] with ConvertAnnots with PCTracking[StateLattice] {
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
                  join, joinStore, joinAssignment, joinLocality,
                  sequence,
                  mkElem}

  
  import pcCommons._
  import pcLattice.{PC, PCInfo, AnyPC}
  
  
  override def newEffectTraverser(rhs: Tree, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit): EffectTraverser =
    new StateTraverser(rhs, EnvMap(), rhsTyper, sym, unit)


  trait Env {
    
    /**
     * Apply an effect to this environemnt.
     * 
     * The `@assign` effects are applied first, which is a conservative result.
     * Example: take a nested function that does both, assigning outer variables
     * and storing values.
     * 
     *   def foo(a: A, b: B, c: C) {
     *     var x = b
     *     def inner() { a.store(x); x = c }
     *     inner()
     *     x
     *   }
     *
     * The effect of `inner` is `@store(a, x) @assign(x, c)`. When applying this
     * effect to the environemnt `x -> {b}`, the assignment effect is treated first.
     * This gives
     *
     *   env(x -> {b})            |  assign(x, c)
     *   env(x -> {b, c})         |  store(a, x)
     *   env(x -> {b, c},
     *       a -> {a, b, c}
     *       b -> {a, b, c}
     *       c -> {a, b, c})
     * 
     * The resulting environemnt is over-approximated, if we knew the store effect
     * happens first, the result would be more precise.
     * 
     * This is correct because an assign can influence a store, but not the other way
     * around; if a store happens before an assign, the assign will already have the
     * merged locality. Example
     * 
     *   def inner() { c.store(a); x = c }
     * 
     * has effect `@store(c, a) @assign(x, (c, a))`.
     * 
     * @TODO: what if there are multiple @assign and / or multiple @store? compute fixpoint?
     */
    def applyEffect(eff: Elem): Env = this match {
      case AnyEnv =>
        AnyEnv

      case EnvMap(m, localsTo) =>
        val assignEnv = eff._2 match {
          case AssignAny(to) =>
            /* Take all local variables (var only, not val!) out of the map `m`, only keep the
             * location map for parameter symbols.
             * Set the `localsTo` accordingly: join of `to`, all localities of local variables
             * in `m`, and the current locality in `localsTo`.
             */
            val (localVarsMap, othersMap) = m.partition(e => e._1.isLocalVar)
            val assignedLocality = (to :: localVarsMap.map(_._2).toList).reduceRight(joinLocality)
            val resLocality = localsTo.map(l => joinLocality(l, assignedLocality)).orElse(Some(assignedLocality))
            EnvMap(othersMap, resLocality)
            
          case assgn @ AssignLoc(strong, weak) =>
            if (localsTo.isDefined) {
              // @TODO: could exclude the localities of assigned locations which are not in scope? should not happen!
              EnvMap(m, localsTo.map(l => joinLocality(l, assgn.assignedLocality)))
            } else {
              val strongMap = (m /: strong) {
                case (m, (to, from)) =>
                  m.updated(to, from)
              }
              val resMap = (strongMap /: weak) {
                case (m, (to, from)) =>
                  val res = m.get(to).map(joinLocality(_, from)).getOrElse(from)
                  m.updated(to, res)
              }
              EnvMap(resMap, localsTo)
            }
        }

        val storeEnv = eff._1 match {
          case StoreAny =>
            AnyEnv

          case StoreLoc(effs) =>
            // @TODO: assumes that the locations in `effs` are parameters / outer variables.
            // if there are local variables, their locality can change over time, and the
            // environment would be not well formed.
            val resMap = (assignEnv.m /: effs) {
              case (m, (in, from)) =>
                from.s.toList match {
                  case Nil | List(Fresh) => m
                  case _ =>
                    // all involved locations
                    val modifiedLocs = from.union(LocSet(in))
                    (m /: modifiedLocs.s) {
                      case (m, loc) => m.updated(loc, modifiedLocs)
                    }
                }
            }
            EnvMap(resMap, assignEnv.localsTo)
        }

        storeEnv
    }
    
    
    def mapLocations(map: Map[Location, Locality]): Env = this match {
        case AnyEnv =>
          AnyEnv
        case EnvMap(m, localsTo) =>
          // in m1 ++ m2, when a key exists in both maps, the value of m2 is picked.
          EnvMap(m ++ map, localsTo)
      }

    /**
     * Look up the locality of a location `loc` in the current environment.
     * 
     * The locality of a non-mapped location depends on the context, therefore
     * this method just returns `None` in that case. Have a look at the method
     * `localityOf` to see the default localities.
     *
     * Note that when analyzing the effect of a method, we start off with an
     * empty environment, where nothing is mapped, and `localityOf` uses the
     * default localities for everything.
     */
    def lookup(loc: Location): Option[Locality] = this match {
      case AnyEnv => Some(AnyLoc)
      case EnvMap(m, localsTo) =>
        if (localsTo.isDefined && loc.isLocalVar) {
          Some(localsTo.get)
        } else {
          m.get(loc)
        }
    }
  }

  /**
   * `m` maps locations (params, local variables) to localities.
   * if `localsTo` is set, this defines the locality of all local variables (i.e. if
   * a `AssignAny(to)` effect occured).
   */
  case class EnvMap(m: Map[Location, Locality] = Map(), localsTo: Option[Locality] = None) extends Env
  case object AnyEnv extends Env

  
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
     */
    val e = super.computeEffect(rhs, rhsTyper, sym, unit)
    val res = e.copy(_2 = e._2 match {
      case aa @ AssignAny(_) => aa
      case AssignLoc(strong, weak) =>
        val strong1 = onlyInScope(strong)
        val weak1 = onlyInScope(weak)
        AssignLoc(strong1, weak1)
    })
    if (res != e) { println("masking assign effect to out-of-scope variables:\n  from: "+ e +"\n  to  : "+ res) }
    res
  }
  
  override def computePrimConstrEffect(impl: Template, implTyper: Typer, classSym: Symbol,
                                      primConstrRhs: Tree, primConstrTyper: Typer, primConstrSym: Symbol,
                                      unit: CompilationUnit): Elem = {
    val refinedRhs = refine(primConstrRhs, primConstrTyper, primConstrSym, unit)
    val rhsEff = new StateTraverser(primConstrRhs, EnvMap(), primConstrTyper, primConstrSym, unit).compute()
    
    val refinedImpl = refine(impl, implTyper, classSym, unit).asInstanceOf[Template]
    val implEnv = EnvMap().applyEffect(rhsEff)
    val implEff = new StateTraverser(impl, implEnv, implTyper, classSym, unit).compute()
    
    lattice.sequence(rhsEff, implEff)
  }

  def subtreeEffect(tree: Tree, env: Env, localTyper: Typer, sym: Symbol, unit: CompilationUnit): Elem = {
    new StateTraverser(tree, env, localTyper, sym, unit).compute()
  }

  class StateTraverser(rhs: Tree, env: Env, rhsTyper: Typer, sym: Symbol, unit: CompilationUnit) extends EffectTraverser(rhs, rhsTyper, sym, unit) {
    def subtreeEffect(tree: Tree, newEnv: Env) = StateChecker.this.subtreeEffect(tree, newEnv, rhsTyper, sym, unit)
    
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
                localityOf(SymLoc(sym), qualEnv, rhsTyper.context1)
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
            if (sym.owner.isRootPackage) add(mkElem(AnyLoc))
            else add(mkElem(localityOf(SymLoc(sym), env, rhsTyper.context1)))
          }


        case Assign(lhs, rhs) =>
          val lhsEffect = subtreeEffect(lhs, env)
          val lhsEnv = env.applyEffect(lhsEffect)
          
          val rhsEffect = subtreeEffect(rhs, lhsEnv)
          // val rhsEnv = lhsEnv.applyEffect(rhsEffect) // not used

          val parts = sequence(lhsEffect, rhsEffect)

          val lhsSym = lhs.symbol
          val owner = lhsSym.owner
     
          val assignmentEffect = if (owner.isClass) {
            // if the lefthand side is a selection of a field, then the assignment has a `@store` effect
            if (owner.isModuleClass) mkElem(StoreAny)
            else {
              // we can assume that we're assigning a field of `this`. all other assignments go through the setter.
              val loc = ThisLoc(owner)
              if (lhsSym.hasAnnotation(localClass)) {
                rhsEffect._3 match {
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
            mkElem(AssignLoc(SymLoc(lhsSym), rhsEffect._3, true))
          }

          val resEff = sequence(parts, assignmentEffect)
          add((resEff._1, resEff._2, LocSet())) // no value is returned, so there's no locality

        case ValDef(mods, name, tpt, rhs) =>
          val sym = tree.symbol
          val rhsEffect = subtreeEffect(rhs, env)
          // the assign effect will be used to set the environemnt correctly
          val assignEffect = mkElem(AssignLoc(SymLoc(sym), rhsEffect._3, true))
          val res = sequence(rhsEffect, assignEffect)
          add((res._1, res._2, LocSet()))

        case Block(stats, expr) =>
          val (statsEff, statsEnv) = ((lattice.bottom, env) /: stats) {
            case ((eff, env), stat) =>
              val e = subtreeEffect(stat, env)
              (sequence(eff, e), env.applyEffect(e))
          }
          
          val exprEff = subtreeEffect(expr, statsEnv)
          add(sequence(statsEff, exprEff))

        case If(cond, thenExpr, elseExpr) =>
          val condEff = subtreeEffect(cond, env)
          val condEnv = env.applyEffect(condEff)
          
          val thenEff = subtreeEffect(thenExpr, condEnv)
          val elseEff = subtreeEffect(elseExpr, condEnv)
          
          val resEff = sequence(condEff, join(thenEff, elseEff))
          add(resEff)
          
        case New(tpt) =>
          // no side effects - the constructor call is represented as a separate Apply tree
          add((StoreLoc(), AssignLoc(), LocSet(Fresh)))
        
        case Super(qual, mix) =>
          add(StoreLoc(), AssignLoc(), LocSet(ThisLoc(tree.symbol)))

        case This(qual) =>
          add(StoreLoc(), AssignLoc(), LocSet(ThisLoc(tree.symbol)))

        case Literal(c) =>
          add(StoreLoc(), AssignLoc(), LocSet(Fresh))
          
        // @TODO
        case Try(block, catches, finalizer) =>
          ()
        
        // @TODO
        case Return(expr) =>
          ()

        // @TODO: CaseDef, Match etc
          
        case _ =>
          super.traverse(tree)
      }
        
    }

    def qualEffect(tree: Tree, env: Env): Elem = tree match {
      case Select(qual, _) => subtreeEffect(qual, env)
      case Ident(_) => lattice.bottom
    }
    
    override def handleApplication(tree: Tree) {
      val (fun, targs, argss) = decomposeApply(tree)
      val funSym = fun.symbol
      
      val funEff = qualEffect(fun, env)
      val funEnv = env.applyEffect(funEff)
      val funLoc = funEff._3 // @TODO: this only works "by chance", because we use "qualEffect", which actually returns the locality of the function's qualifier. maybe just rename "funLoc" to "qualLoc" to make things clear.
      
      // foldRight traverses left to right (that's the order in which
      // effects happen, the order of evaluation for the arguments).
      val (targsEff, targsEnv /*, targLocs*/) = ((funEff, funEnv/*, List[Locality]()*/) /: targs) {
        case ((eff, env/*, locs*/), targ) =>
          val e = subtreeEffect(targ, env)
          (sequence(eff, e), env.applyEffect(e)/*, e._3 :: locs*/)
      }
          
      val (argssEff, argssEnv, flatArgLocs) = ((targsEff, targsEnv, List[Locality]()) /: argss.flatten) {
        case ((eff, env, locs), arg) =>
          val e = subtreeEffect(arg, env)
          (sequence(eff, e), env.applyEffect(e), e._3 :: locs)
      }
      
      // build a map from the function's parameter symbols to the localities of the arguments
      val flatParams = funSym.tpe.paramss.flatten

      val paramsMap: Map[Location, Locality] = {
        // For methods in classes (not objects), modifications to `this` mean modifications to the receiver (funLoc)
        val receiverMap = if (funSym.owner.isModuleClass) Map() else Map(ThisLoc(funSym.owner) -> funLoc)
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
      val applyEnv = argssEnv.mapLocations(paramsMap)

      withEnv(applyEnv) {
        val fromApp = computeApplicationEffect(fun, targs, argss) 
        val res = sequence(argssEff, fromApp)
        add((res._1, res._2, fromApp._3))
      }
    }
    
    override def computeApplicationEffect(fun: Tree, targs: List[Tree] = Nil, argss: List[List[Tree]] = Nil) = {
      val latent = latentEffect(fun, targs, argss, rhsTyper.context1)
      val mappedLatent = adaptLatentEffect(latent, fun, targs, argss, rhsTyper.context1)
      val mappedPc = adaptToEffectPolymorphism(mappedLatent, fun, targs, argss, rhsTyper.context1)
      
      /* Effect polymorphism is not applied to the `@loc` effects, they are kept monomorphic. Example:
       * 
       *   def foo(a: A, b: B) @pc(a.bar(), b.baz()) = {
       *     a.bar()
       *     b.baz()
       *   }
       * 
       * Looking at the `@pc` effects, we cannot see the returned locality.
       * Maybe the `@loc` annotations can be extended in future to support something like
       * `@loc(b.baz())`.
       */
      (mappedPc._1, mappedPc._2, mappedLatent._3)
    }
  }
  
  private var currentEnv: Env = null
  def withEnv[T](env: Env)(op: => T): T = {
    val savedEnv = currentEnv
    currentEnv = env
    val res = op
    currentEnv = savedEnv
    res
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
    
  override def adaptPcEffect(eff: Elem, pc: PCInfo, fun: Tree, targs: List[Tree], argss: List[List[Tree]], ctx: Context): Elem = {
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
     *   fun   = qual.foo
     *   argss = (arg)
     * 
     * We have to map the localities of `@mod(this) @mod(b)`. The correct
     * locality map to apply is the following:
     * 
     *   this -> { localityOf(arg) }
     *   b    -> AnyLoc
     */
    val paramLoc = SymLoc(pc.param)
    // @TODO: fix when enabling PC calls on `this`

    val thisLocality = currentEnv.lookup(paramLoc).getOrElse(abort("parameter not in locations map: "+ paramLoc +", "+ currentEnv))
    val map: Map[Location, Locality] = Map(ThisLoc(pc.fun.owner) -> thisLocality) ++ (pc.fun.paramss.flatten.map(p => SymLoc(p) -> AnyLoc))
    val pcEnv = currentEnv.mapLocations(map)
    mapLocalities(eff, pcEnv, ctx)
  }

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
      case AssignLoc(strong, weak) =>
        val mapStrong = strong.map(e => (e._1, mapLocality(e._2, env, ctx)))
        val mapWeak = weak.map(e => (e._1, mapLocality(e._2, env, ctx)))
        AssignLoc(mapStrong, mapWeak)
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
   * The locality of a selected symbol.
   * 
   *  - if the symbol is a parameter of the current method, or a local value / variable
   *    defined in the current method, then look up the locality in the environment
   *
   *  - if the symbol is a parameter of an outer method, or a local value / variable
   *    defined in an outer method, SymLoc(sym)
   *
   *  - if the symbol is anything else, AnyLoc
   */
  def localityOf(loc: Location, env: Env, ctx: Context): Locality = loc match {
    case SymLoc(sym) =>
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
      println("locality of "+ sym +" is "+ res)
      res

    case ThisLoc(_) =>
      /* @TODO: what's a good default? basically, the default should never happen
       * to be used. When we look up the locality for a select or ident, then it's
       * always a SymLoc. When looking up the locality of a ThisLoc, it can only
       * be during `adaptLatentEffect` or `adaptPcEffect`, and then the `ThisLoc`
       * should be present.
       */
      env.lookup(loc).getOrElse(LocSet(loc))

    case Fresh =>
      // @TODO: can this case ever arise? see comment above.
      LocSet(Fresh)
  }
}
