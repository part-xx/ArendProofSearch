package typechecker.coreapi.proofstep

import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.Definition
import org.arend.core.definition.TopLevelDefinition
import org.arend.ext.error.GeneralError
import org.arend.ext.module.ModuleLocation
import org.arend.ext.module.ModulePath
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.Referable
import org.arend.naming.scope.Scope
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import typechecker.Proof
import typechecker.ProofStep
import typechecker.coreapi.ArendGoal
import kotlin.math.max
import kotlin.math.min

/** The kinds of steps [HeuristicStepGenerator] proposes. */
enum class Heuristic {
  /** `idp`, a hypothesis, or `contradiction`: closes the goal ([ClosingGenerator]). */
  CLOSE,
  /** A retrieved premise applied to subgoals ([AppGenerator]). */
  APPLY,
  /** Case analysis ([CaseGenerator]). */
  CASE,
  /** Rewriting with an equation ([RewriteGenerator]). */
  REWRITE,
  /** The recursive call inside a `\case \elim` branch ([InductionGenerator]). */
  INDUCTION,
  /** `pmap f` for a goal `f a = f a'` ([CongruenceGenerator]). */
  CONGRUENCE,
  /** `ext {?}` for an equality of functions, pairs, records or propositions ([ExtGenerator]). */
  EXT,
  /** A hypothesis of a function type applied, or refuting the goal with one ([HypothesisGenerator]). */
  HYPOTHESIS,
  /** `\lam x => {?}` for a goal of a function type ([IntroGenerator]). */
  INTRO,
  /** `({?}, {?})` for a goal `\Sigma A B` ([TupleGenerator]). */
  TUPLE,
  /** `unfold f {?}` for a function of the goal defined by an expression ([UnfoldGenerator]). */
  UNFOLD,
  /** `transport (n mod m <=) (divModProp n m) {?}`: a relation along an equation at one argument ([TransportGenerator]). */
  TRANSPORT,
  /** `pmap pred p` for `p : suc a = suc b` and a goal `a = b` ([InjectivityGenerator]). */
  INJECTIVITY,
}

/**
 * Combines the heuristic step generators. Premises to apply are selected by [retrievers], and
 * library equations to rewrite with by [rewriteRetrievers]; in both cases the candidates that
 * resolve to finished definitions and fit the goal ([ConclusionMatcher]) are ranked, and the
 * [maxPremises] best are used.
 *
 * Metas and decision functions come from arend-lib; the steps that need them are skipped when
 * they cannot be resolved, e.g. in a library that does not depend on arend-lib.
 */
class HeuristicStepGenerator(
  checker: ArendChecker,
  server: ArendServer,
  libName: String,
  modulePath: ModulePath,
  private val retrievers: List<PremiseRetriever> = listOf(FixedPremiseRetriever(listOf("TotalOrder.meet-isMin"))),
  private val maxPremises: Int = 80,
  private val heuristics: Set<Heuristic> = Heuristic.entries.toSet(),
  private val rewriteRetrievers: List<PremiseRetriever> = emptyList(),
  /** Decision functions to split on, each with its cost; the defaults cost more than ones selected for the goal. */
  private val splitters: List<PremiseCandidate> = DEFAULT_SPLITTERS,
  /** Selects library lemmas concluding a disjunction or a truncated existence to split on ([SplitRetriever]). */
  private val splitRetrievers: List<PremiseRetriever> = emptyList(),
  /** Selects functions to map a same-headed hypothesis equation over ([DestructorRetriever]). */
  private val destructorRetrievers: List<PremiseRetriever> = emptyList(),
  /** Selects lemmas of a twin structure, applied with the converted instance ([TransferRetriever]); made by [transferRetriever]. */
  private val transferRetrieverFactory: ((List<TransferRetriever.Conversion>) -> TransferRetriever)? = null,
  /** Metas that close a goal, with their costs; the solvers are slow and prove much, so tests of a particular step may leave them out. */
  private val closingMetas: List<PremiseCandidate> = DEFAULT_CLOSING_METAS,
): BaseStepGenerator(checker, server, libName, modulePath) {
  companion object {
    /** The functions arend-lib proofs most often split on, most frequent first. */
    val DEFAULT_SPLITTERS = listOf(
      "DecSet.decideEq" to "Set",
      "LinearOrder.dec<_<=" to "Order.LinearOrder",
      "LinearOrder.<=-dec" to "Order.LinearOrder",
      "LinearOrder.Dec.trichotomy" to "Order.LinearOrder",
      "TotalOrder.totality" to "Order.LinearOrder",
      "TotalOrder.meet-isMin" to "Order.LinearOrder",
      "TotalOrder.join-isMax" to "Order.LinearOrder",
    ).map { (name, module) -> PremiseCandidate(name, module, CaseGenerator.SPLITTER_COST) }

    val BASIC_CLOSING_METAS = listOf(PremiseCandidate("contradiction", "Logic.Meta", 0.0))

    /** The basic closers and arend-lib's solvers, in the order they are tried. */
    val DEFAULT_CLOSING_METAS = BASIC_CLOSING_METAS + listOf(
      PremiseCandidate("equation", "Algebra.Meta", 0.3),
      PremiseCandidate("linarith", "Algebra.Meta", 0.3),
    )



    /** Subtracted from a premise's cost for each definition its conclusion matches in the goal ([ConclusionMatcher]). */
    const val SPECIFICITY_BONUS = 0.2
    /**
     * Added to a premise whose conclusion matches the goal only by its head, as `=_<= : x = y -> x <= y`
     * or `inv : a = b -> b = a` do any `<=` or `=` goal: such premises fit every goal and lead nowhere
     * in particular, so premises shaped after the goal are tried first.
     */
    const val GENERIC_PENALTY = 0.4

    private val sharedCaches = java.util.WeakHashMap<Any, Caches>()
    /** Added to an equation applied backwards, `inv L`. */
    const val REVERSED_COST = 0.1
    /**
     * Added to a premise from a theory the goal is not about: the first component of its module
     * (`Topology`, `Algebra`, `Order`, `Arith`) is not that of any definition in the goal or its
     * context. Proof search finds every lemma concluding `<=` in the library; the ones about
     * locales or matrices fit a goal about naturals only by their head.
     */
    const val FOREIGN_THEORY_PENALTY = 0.5
    /**
     * Subtracted from a premise one of whose parameters is shaped like a hypothesis of the context
     * beyond its head (`x + y = 0` for `x-y=0 : x - y = 0`): the premise consumes what the goal has.
     */
    const val HYPOTHESIS_FIT_BONUS = 0.3
    /** Taken off an injectivity lemma of the goal's equation's type (`fin_nat-inj` for an equation in `Fin n`). */
    const val INJECTIVITY_BONUS = 0.3
    /** A parameter has to match a hypothesis at least this specifically for [HYPOTHESIS_FIT_BONUS]. */
    const val HYPOTHESIS_FIT_SCORE = 2
    const val MAX_SPECIFICITY = 5
    /** Subtracted from a premise that closes the goal outright, with no subgoal to prove: most proofs end with one. */
    const val CLOSING_BONUS = 0.3
    const val MIN_PREMISE_COST = 0.1
    const val FIT_CACHE_SIZE = 300_000
    const val RESOLVED_MEMO_SIZE = 4_000
    const val REJECTED_CACHE_SIZE = 3_000
    /** A single candidate's resolution or fit taking longer than this is reported: it is what makes a search overrun its clock. */
    const val SLOW_CANDIDATE_MILLIS = 2000
    /** Step generation at least this slow is logged with the time each phase took. */
    const val SLOW_GENERATION_MILLIS = 2000
  }

  private val scopes = HashMap<String?, Scope?>()

  private fun scope(module: String?): Scope? = scopes.getOrPut(module) {
    if (module == null) getScope() else getScope(ModulePath.fromString(module))
  }

  /** The typechecked definition named by [candidate], or the referable itself for metas, which have no definition. */
  private fun resolve(candidate: PremiseCandidate): Referable? =
    scope(candidate.module)?.let { resolveName(it, candidate.name) ?: resolveReferable(it, candidate.name) }

  private val closingMetaRefs: List<Pair<ArendRef, Double>> by lazy { closingMetas.mapNotNull { candidate -> resolve(candidate)?.let { it to candidate.cost } } }
  /** arend-lib's conversions between twin structures, for [TransferRetriever]. */
  private val conversions: List<TransferRetriever.Conversion> by lazy {
    listOf(
      "AddMonoid.fromMonoid" to "Algebra.Monoid", "AddMonoid.toMonoid" to "Algebra.Monoid", "AbMonoid.fromCMonoid" to "Algebra.Monoid", "AbMonoid.toCMonoid" to "Algebra.Monoid",
      "AddGroup.fromGroup" to "Algebra.Group", "AddGroup.toGroup" to "Algebra.Group", "AbGroup.fromCGroup" to "Algebra.Group", "AbGroup.toCGroup" to "Algebra.Group",
      "BottomJoinSemilattice.toMonoid" to "Order.Lattice", "TopMeetSemilattice.toMonoid" to "Order.Lattice",
    ).mapNotNull { (name, module) ->
      ((resolve(PremiseCandidate(name, module)) as? org.arend.naming.reference.TCDefReferable)?.typechecked as? org.arend.core.definition.FunctionDefinition)?.let { TransferRetriever.conversion(it) }
    }
  }
  private val transferRetriever: TransferRetriever? by lazy { transferRetrieverFactory?.invoke(conversions) }

  /** arend-lib's specialized equation solvers with their classes, most specific first. */
  private val equationSolvers: List<ClosingGenerator.Solver> by lazy {
    if (closingMetas.none { it.name == "equation" }) emptyList() else listOf(
      "cRing" to ("CRing" to "Algebra.Ring"), "ring" to ("Ring" to "Algebra.Ring"),
      "cSemiring" to ("CSemiring" to "Algebra.Semiring"), "semiring" to ("Semiring" to "Algebra.Semiring"),
      "abGroup" to ("AbGroup" to "Algebra.Group"), "cGroup" to ("CGroup" to "Algebra.Group"), "addGroup" to ("AddGroup" to "Algebra.Group"), "group" to ("Group" to "Algebra.Group"),
      "abMonoid" to ("AbMonoid" to "Algebra.Monoid"), "cMonoid" to ("CMonoid" to "Algebra.Monoid"), "addMonoid" to ("AddMonoid" to "Algebra.Monoid"), "monoid" to ("Monoid" to "Algebra.Monoid"),
      "cSemigroup" to ("CSemigroup" to "Algebra.Monoid"), "semigroup" to ("Semigroup" to "Algebra.Monoid"),
    ).mapNotNull { (solver, cls) ->
      val meta = resolve(PremiseCandidate("equation.$solver", "Algebra.Meta")) ?: return@mapNotNull null
      val definition = (resolve(PremiseCandidate(cls.first, cls.second)) as? org.arend.naming.reference.TCDefReferable)?.typechecked as? org.arend.core.definition.ClassDefinition ?: return@mapNotNull null
      ClosingGenerator.Solver(meta, definition)
    }
  }
  private val unfoldRef: ArendRef? by lazy { resolve(PremiseCandidate("unfold", "Meta")) }
  private val usingRef: ArendRef? by lazy { resolve(PremiseCandidate("using", "Meta")) }
  private val extRef: ArendRef? by lazy { resolve(PremiseCandidate("ext", "Paths.Meta")) }
  private val concatRef: ArendRef? by lazy { resolve(PremiseCandidate("*>", "Paths")) }
  private val invRef: ArendRef? by lazy { resolve(PremiseCandidate("inv", "Paths")) }
  private val mcasesRef: ArendRef? by lazy { resolve(PremiseCandidate("mcases", "Meta")) }
  private val pmapRef: ArendRef? by lazy { resolve(PremiseCandidate("pmap", "Paths")) }
  private val absurdRef: ArendRef? by lazy { resolve(PremiseCandidate("absurd", "Logic")) }
  /** Transitivity operators for chains through the induction hypothesis: orders' `<=∘` and paths' `*>`. */
  private val chainRefs: List<ArendRef> by lazy { listOfNotNull(resolve(PremiseCandidate("Preorder.<=-transitive", "Order.PartialOrder")), concatRef) }
  private val transportRefs: Pair<ArendRef, ArendRef>? by lazy {
    val transport = resolve(PremiseCandidate("transport", "Paths")) ?: return@lazy null
    val transportInv = resolve(PremiseCandidate("transportInv", "Paths")) ?: return@lazy null
    transport to transportInv
  }
  /** Paths' `transport2`, for a relation lemma brought to the goal by equations at both arguments ([RelationFixGenerator]). */
  private val transport2Ref: ArendRef? by lazy { resolve(PremiseCandidate("transport2", "Paths")) }
  private val splitterRefs: List<Pair<ArendRef, Double>> by lazy {
    splitters.mapNotNull { candidate -> resolve(candidate)?.let { it to candidate.cost } }
  }
  private val rewriteMetas: RewriteMetas? by lazy {
    val rewrite = resolve(PremiseCandidate("rewrite", "Paths.Meta")) ?: return@lazy null
    val rewriteI = resolve(PremiseCandidate("rewriteI", "Paths.Meta")) ?: return@lazy null
    RewriteMetas(rewrite, rewriteI, resolve(PremiseCandidate("in", "Meta")))
  }

  private val debug = System.getProperty("proofsearch.debug") == "true"

  /**
   * For each goal statement (type and context, as printed), the premises whose application was
   * rejected on it: the same statement comes up again in sibling branches and in other proof
   * states, and rejection depends only on the statement.
   */
  private val rejectedPremises: MutableMap<String, MutableSet<CallableDefinition>> get() = caches.rejectedPremises

  /** How each premise fits each goal type seen (apply, reversed, rewrite): the same goal types recur across proof states. */
  /** Stands for "does not fit" in [Caches.fitCache]: `getOrPut` cannot cache a null, and most premises do not fit. */
  private val NO_FIT = Int.MIN_VALUE
  private fun cachedFit(key: Triple<String, String, CallableDefinition>, compute: () -> Int?): Int? =
    caches.fitCache.getOrPut(key) { compute() ?: NO_FIT }.takeIf { it != NO_FIT }

  /**
   * What is learned about the library's definitions does not depend on the goal: resolving a retrieved
   * name to a definition, how a definition fits a goal statement, which were rejected on a statement.
   * It is kept per typechecking server, across the generators made for the lemmas of a benchmark.
   */
  private object NOT_USABLE

  private class Caches {
    /** A [CallableDefinition], or [NOT_USABLE]: `getOrPut` cannot cache a null. */
    val usableDefinitions = HashMap<Pair<String?, String>, Any>()
    // Bounded, least recently used first out: over a benchmark of hundreds of lemmas these would otherwise hold
    // millions of entries and starve the heap, which showed as searches running for minutes
    val fitCache: MutableMap<Triple<String, String, CallableDefinition>, Int> = lru(FIT_CACHE_SIZE)
    val rejectedPremises: MutableMap<String, MutableSet<CallableDefinition>> = lru(REJECTED_CACHE_SIZE)
    /** Whether a definition consumes a hypothesis of a type, by the type's text: the same hypotheses recur across proof states. */
    val hypothesisFits: MutableMap<Pair<CallableDefinition, String>, Boolean> = lru(FIT_CACHE_SIZE)

    private fun <K, V> lru(size: Int): MutableMap<K, V> = object : LinkedHashMap<K, V>(1024, 0.75f, true) {
      override fun removeEldestEntry(eldest: MutableMap.MutableEntry<K, V>?): Boolean = this.size > size
    }
  }

  private val caches: Caches = synchronized(sharedCaches) { sharedCaches.getOrPut(server) { Caches() } }

  /** Retrieved candidates resolved to definitions that may be used, by module and name; retrieval proposes the same ones for many goals. */
  private fun usableDefinition(goal: ArendGoal, candidate: PremiseCandidate): CallableDefinition? {
    // A candidate without a module resolves in the module being proved, so it is not shared
    if (candidate.module == null) return resolveUnshared(goal, candidate)
    val key = candidate.module to candidate.name
    caches.usableDefinitions[key]?.let { return it as? CallableDefinition }
    // A name not resolved or not typechecked yet may be later (the library is typechecked as the searches go): not remembered
    val result = computeUsableDefinition(goal, candidate) ?: return null
    caches.usableDefinitions[key] = result
    return result as? CallableDefinition
  }

  /** The definition, [NOT_USABLE] for a definition that never will be, or null when it cannot be told yet. */
  private fun computeUsableDefinition(goal: ArendGoal, candidate: PremiseCandidate): Any? =
    run {
      // Retrieval proposes thousands of definitions: those not typechecked yet are not worth typechecking
      val tcReferable = resolveName(scope(candidate.module!!) ?: return@run null, candidate.name, typecheck = false) ?: return@run null
      val definition = getCallableDefinition(goal, tcReferable) ?: return@run null
      when {
        // A `\private` lemma of another proof (`intCoef-surj.aux`) cannot be referred to from outside: the CLI rejects such proofs
        tcReferable.accessModifier == org.arend.term.group.AccessModifier.PRIVATE -> NOT_USABLE
        // Unfinished definitions would make the proof incomplete
        definition.status().hasErrors() || hasGoals(definition) -> NOT_USABLE
        // An axiom such as `alem` (excluded middle) proves its goals outright, and so does a lemma derived
        // from one, such as `lemFromChoice`; a proof should not depend on an axiom unasked
        (definition as? TopLevelDefinition)?.isAxiom == true || definition.axioms.isNotEmpty() -> NOT_USABLE
        else -> definition
      }
    }

  private val unsharedDefinitions = HashMap<Pair<String?, String>, CallableDefinition?>()

  private fun resolveUnshared(goal: ArendGoal, candidate: PremiseCandidate): CallableDefinition? =
    unsharedDefinitions.getOrPut(candidate.module to candidate.name) {
      // Retrieval proposes thousands of definitions: those not typechecked yet are not worth typechecking
      val tcReferable = resolveName(scope(candidate.module) ?: return@getOrPut null, candidate.name, typecheck = false) ?: return@getOrPut null
      val definition = getCallableDefinition(goal, tcReferable) ?: return@getOrPut null
      when {
        // A `\private` lemma of another proof (`intCoef-surj.aux`) cannot be referred to from outside: the CLI rejects such proofs
        tcReferable.accessModifier == org.arend.term.group.AccessModifier.PRIVATE -> null
        // Unfinished definitions would make the proof incomplete
        definition.status().hasErrors() || hasGoals(definition) -> null
        // An axiom such as `alem` (excluded middle) proves its goals outright, and so does a lemma derived
        // from one, such as `lemFromChoice`; a proof should not depend on an axiom unasked
        (definition as? TopLevelDefinition)?.isAxiom == true || definition.axioms.isNotEmpty() -> null
        else -> definition
      }
    }

  /**
   * Resolves [candidates] to definitions, keeping each definition's lowest cost. With [fit], only
   * the definitions that fit the goal are kept, and the more specifically one fits, the less it
   * costs; the [maxPremises] cheapest are returned.
   */
  fun resolvePremises(
    goal: ArendGoal, candidates: List<PremiseCandidate>,
    fit: ((CallableDefinition) -> Int?)? = null,
    closes: ((CallableDefinition) -> Boolean)? = null,
    /** Whether premises that fit the goal only by its head pay [GENERIC_PENALTY]. */
    penalizeGeneric: Boolean = false,
    /** How many of the cheapest premises are returned. */
    limit: Int = maxPremises,
    /** With a label, the result is remembered for the problem: the same statement over the same context recurs across proof states. */
    memo: String? = null,
  ): Map<CallableDefinition, Double> {
    // Keyed by the candidates too: a symbol first met inside a search is indexed in the background, so the same
    // problem may get more candidates later (`pred` for `x = {Nat} y` once Nat's destructors arrive)
    val memoKey = if (System.getProperty("proofsearch.noResolveMemo") == "true") null else memo?.let { Triple(it, goal.problemText, candidates.hashCode()) }
    if (memoKey != null) resolvedPremises[memoKey]?.let { return it }
    val result = computePremises(goal, candidates, fit, closes, penalizeGeneric, limit)
    if (memoKey != null) resolvedPremises[memoKey] = result
    return result
  }

  /** Resolved premises by (label, problem), per generator: a benchmark's exclusions differ between lemmas. */
  private val resolvedPremises: MutableMap<Triple<String, String, Int>, Map<CallableDefinition, Double>> = object : LinkedHashMap<Triple<String, String, Int>, Map<CallableDefinition, Double>>(256, 0.75f, true) {
    override fun removeEldestEntry(eldest: MutableMap.MutableEntry<Triple<String, String, Int>, Map<CallableDefinition, Double>>?): Boolean = size > RESOLVED_MEMO_SIZE
  }

  private fun computePremises(
    goal: ArendGoal, candidates: List<PremiseCandidate>, fit: ((CallableDefinition) -> Int?)?, closes: ((CallableDefinition) -> Boolean)?,
    penalizeGeneric: Boolean, limit: Int,
  ): Map<CallableDefinition, Double> {
    // In candidate order, so that equally good premises are ranked the same in every run
    val premises = LinkedHashMap<CallableDefinition, Double>()
    val resolveStart = System.nanoTime()
    var fitNanos = 0L
    var usableNanos = 0L
    var bonusNanos = 0L
    val theories = goalTheories(goal)
    val goalEquationHead = RewriteGenerator.equationType(goal.expectedType)?.let { PremiseRetriever.headKey(it) }
    val hypothesisTypes = goal.typechecker.context.values.map { it.type }.filter { it.sortOfType?.isProp == true || it.normalize(org.arend.ext.core.ops.NormalizationMode.WHNF) is org.arend.core.expr.DataCallExpression }
      .map { it to it.toString() }
    for (candidate in candidates) {
      val candidateStart = System.currentTimeMillis()
      val usableStart = System.nanoTime()
      val definition = usableDefinition(goal, candidate)
      usableNanos += System.nanoTime() - usableStart
      if (System.currentTimeMillis() - candidateStart > SLOW_CANDIDATE_MILLIS) println("Slow resolution (${System.currentTimeMillis() - candidateStart}ms): $candidate")
      if (definition == null) {
        if (debug) println("Dropped candidate $candidate: not a usable definition")
        continue
      }
      // The definition being proved would make the proof circular
      if (definition == goal.definition) continue
      val fitStart = System.currentTimeMillis()
      val fitStartNanos = System.nanoTime()
      val score = if (fit == null) 0 else fit(definition) ?: run { if (debug) println("Dropped candidate $candidate: ${ConclusionMatcher.conclusion(definition)} does not fit ${goal.expectedType}"); null }
      fitNanos += System.nanoTime() - fitStartNanos
      if (System.currentTimeMillis() - fitStart > SLOW_CANDIDATE_MILLIS) println("Slow fit (${System.currentTimeMillis() - fitStart}ms): $candidate against ${goal.expectedType}")
      if (score == null) continue
      val closingBonus = if (closes != null && closes(definition)) CLOSING_BONUS else 0.0
      // `x = y` between bare parameters is generic, unless the parameters are of the goal's equation's own type and the
      // lemma asks for an equation between them in another: `fin_nat-inj : x = {Nat} y -> x = y` for `x y : Fin n` is
      // how arend-lib proves equations in `Fin` (`mod_suc`, `fin_mod_id`, `nat_fin_=`), not a generic lemma
      val injective = score <= 1 && goalEquationHead != null && System.getenv("AREND_PS_NO_INJECTIVITY") == null && injectivityLemma(definition, goalEquationHead)
      val genericPenalty = if (penalizeGeneric && score <= 1 && closingBonus == 0.0 && !injective) GENERIC_PENALTY else 0.0
      val injectivityBonus = if (injective) INJECTIVITY_BONUS else 0.0
      val theory = definition.ref.location?.modulePath?.firstName
      val foreignPenalty = if (theories.isNotEmpty() && theory != null && theory !in theories) FOREIGN_THEORY_PENALTY else 0.0
      val bonusStart = System.nanoTime()
      val hypothesisBonus = if (penalizeGeneric && hypothesisTypes.any { (type, text) -> caches.hypothesisFits.getOrPut(definition to text) { consumesHypothesis(definition, listOf(type)) } }) HYPOTHESIS_FIT_BONUS else 0.0
      bonusNanos += System.nanoTime() - bonusStart
      val cost = max(MIN_PREMISE_COST, candidate.cost - SPECIFICITY_BONUS * min(score, MAX_SPECIFICITY) - closingBonus + genericPenalty + foreignPenalty - hypothesisBonus - injectivityBonus)
      if (debug && fit != null) println("Premise ${definition.ref.refName}: cost %.2f = candidate %.2f, score $score, closing $closingBonus, generic $genericPenalty, foreign $foreignPenalty, hypothesis $hypothesisBonus, injective $injectivityBonus".format(cost, candidate.cost))
      if (premises[definition]?.let { it <= cost } != true) premises[definition] = cost
    }
    if (StepBuilder.timing && System.nanoTime() - resolveStart > 10_000_000L) {
      println("Resolve ${candidates.size} candidates in ${(System.nanoTime() - resolveStart) / 1_000_000}ms: usable ${usableNanos / 1_000_000}ms, fit ${fitNanos / 1_000_000}ms, hypothesis bonus ${bonusNanos / 1_000_000}ms, ${premises.size} kept")
    }
    return premises.entries.sortedBy { it.value }.take(limit).associateTo(LinkedHashMap()) { it.key to it.value }
  }

  /**
   * Whether [definition] concludes `x = y` for bare parameters of a type headed by [equationHead] from an explicit
   * parameter equating the same `x` and `y` in another type: injectivity of a coercion, `fin_nat-inj : x = {Nat} y -> x = y`.
   */
  private fun injectivityLemma(definition: CallableDefinition, equationHead: Any): Boolean {
    val (left, right) = ConclusionMatcher.conclusion(definition)?.let { RewriteGenerator.equationSidesAsWritten(it) } ?: return false
    if (left !is org.arend.core.expr.ReferenceExpression || right !is org.arend.core.expr.ReferenceExpression || left.binding == right.binding) return false
    if (PremiseRetriever.headKey(left.binding.type) != equationHead) return false
    // The hypothesis equates the same two variables (in another type): `unsuc : suc n = suc m -> n = m` is not this, and
    // rewarded it would be applied again and again, each time growing the equation
    return RelationFixGenerator.explicitParameters(definition).any { parameter ->
      val sides = RewriteGenerator.equationSidesAsWritten(parameter.type) ?: return@any false
      (sides.first as? org.arend.core.expr.ReferenceExpression)?.binding == left.binding && (sides.second as? org.arend.core.expr.ReferenceExpression)?.binding == right.binding
    }
  }

  /** Whether an explicit parameter of [definition] is shaped like one of [hypothesisTypes], beyond its head. */
  private fun consumesHypothesis(definition: CallableDefinition, hypothesisTypes: List<org.arend.core.expr.Expression>): Boolean {
    if (hypothesisTypes.isEmpty()) return false
    val parameters = when (definition) {
      is org.arend.core.definition.FunctionDefinition -> org.arend.core.context.param.DependentLink.Helper.toList(definition.parameters)
      is org.arend.core.definition.ClassField -> generateSequence(definition.type.codomain) { (it as? org.arend.core.expr.PiExpression)?.codomain }
        .filterIsInstance<org.arend.core.expr.PiExpression>().flatMap { org.arend.core.context.param.DependentLink.Helper.toList(it.parameters) }.toList()
      else -> return false
    }
    return parameters.filter { it.isExplicit }.any { param -> hypothesisTypes.any { (ConclusionMatcher.match(param.type, it) ?: -1) >= HYPOTHESIS_FIT_SCORE } }
  }

  /** The theories the goal is about: the first module components of the definitions in its type and context. */
  private fun goalTheories(goal: ArendGoal): Set<String> {
    val theories = HashSet<String>()
    val visitor = object : org.arend.core.expr.visitor.VoidExpressionVisitor<Void?>() {
      override fun visitDefCall(expr: org.arend.core.expr.DefCallExpression, params: Void?): Void? {
        expr.definition.ref.location?.modulePath?.firstName?.let { theories.add(it) }
        return super.visitDefCall(expr, params)
      }
    }
    goal.expectedType.accept(visitor, null)
    goal.typechecker.context.values.forEach { it.type.accept(visitor, null) }
    return theories
  }

  private val definitionsWithGoals = HashMap<ModuleLocation?, Set<ArendRef>>()

  /**
   * Whether [definition] still has goals. Lemma bodies are not kept in core; the definition records
   * its goals, and the server's errors do too, until its module is typechecked again.
   */
  private fun hasGoals(definition: Definition): Boolean {
    if (definition.goals.isNotEmpty()) return true
    val module = definition.ref.location
    val withGoals = definitionsWithGoals.getOrPut(module) {
      if (module == null) return@getOrPut emptySet()
      val refs = HashSet<ArendRef>()
      for (error in server.getTypecheckingErrors(module)) {
        if (error.level == GeneralError.Level.GOAL) error.forAffectedDefinitions { ref, _ -> refs.add(ref) }
      }
      refs
    }
    return definition.ref in withGoals
  }

  /** The name of the parameter a class lemma or field takes its instance in. */
  private fun instanceParameterName(premise: CallableDefinition): String? = when (premise) {
    is org.arend.core.definition.FunctionDefinition -> premise.parameters.takeIf { it.hasNext() && !it.isExplicit }?.name
    is org.arend.core.definition.ClassField -> premise.type.parameters.name
    else -> null
  }

  /** The class whose instance a class lemma or field takes first, as `CancelMonoid` for `cancel_*-left`, or null. */
  private fun instanceClassOf(premise: CallableDefinition): org.arend.core.definition.ClassDefinition? {
    val parameter = when (premise) {
      is org.arend.core.definition.FunctionDefinition -> premise.parameters.takeIf { it.hasNext() && !it.isExplicit }
      is org.arend.core.definition.ClassField -> premise.type.parameters
      else -> null
    } ?: return null
    return (parameter.type.normalize(org.arend.ext.core.ops.NormalizationMode.WHNF) as? org.arend.core.expr.ClassCallExpression)?.definition
  }

  /** The twin symbols of the goal under arend-lib's conversions, for indexing them before a timed search. */
  fun transferSymbols(goal: ArendGoal): List<String> = transferRetriever?.symbols(goal) ?: emptyList()

  /**
   * The lemma instances a solver is hinted with for [goal] ([LemmaHints]): the retrieved equations about the goal's
   * functions whose explicit parameters are propositions, applied to the hypotheses (`pow-comm1 p`, `pow-comm1 (inv p)`).
   */
  fun lemmaHints(goal: ArendGoal): List<org.arend.ext.concrete.expr.ConcreteExpression> {
    val candidates = rewriteRetrievers.flatMap { it.retrieve(goal) }
    val lemmas = resolvePremises(goal, candidates, memo = "hint").keys.filter { LemmaHints.propositionParameters(it) != null }
    return LemmaHints.instances(goal, lemmas, invRef)
  }

  /** The scope of the module being proved, for writing proofs in it. */
  fun moduleScope(): Scope? = getScope()

  override fun setDeadline(deadlineMillis: Long) {
    StepBuilder.deadline = deadlineMillis
  }

  /**
   * Resolves what retrieval proposes for [goal] to definitions without generating steps: the
   * resolution is library-wide work shared by every later goal, and so belongs to indexing rather
   * than to a search's budget.
   */
  fun warmUp(goal: ArendGoal) {
    (retrievers + rewriteRetrievers).flatMap { it.retrieve(goal) }.forEach { usableDefinition(goal, it) }
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> =
    // Under the deadline's cancellation indicator throughout: a normalization or a typecheck that would run
    // for minutes (Arend checks the indicator in both) is interrupted when the lemma's clock runs out
    StepBuilder.withDeadline { generateSteps(goal, currentProof) }
      ?: run { println("Step generation interrupted by the deadline for goal ${goal.expectedType}"); emptyList() }

  private fun generateSteps(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val moduleLocation = getModuleLocation() ?: return emptyList()
    val timings = mutableListOf<String>()
    val start = System.currentTimeMillis()
    fun <T> timed(label: String, fallback: T? = null, block: () -> T): T {
      val before = System.currentTimeMillis()
      val result = try { block() } catch (e: StackOverflowError) {
        // One heuristic's evaluator blowing the stack on a huge term should not cost the lemma the rest of its steps
        println("Stack overflow in $label for goal ${goal.expectedType}")
        fallback ?: throw e
      }
      val millis = System.currentTimeMillis() - before
      if (millis >= 500 || StepBuilder.timing) timings.add("$label ${millis}ms")
      if (millis >= StepBuilder.SLOW_TYPECHECK_MILLIS) println("Slow $label (${millis}ms) for goal ${goal.expectedType}")
      return result
    }
    fun report() {
      val total = System.currentTimeMillis() - start
      if (total >= SLOW_GENERATION_MILLIS || StepBuilder.timing) println("Step generation (${total}ms): ${timings.joinToString()} for goal ${goal.expectedType}")
    }

    // Lemma instances for a solver's hints (`equation.monoid {p, pow-comm1 p}`): the library equations about the goal's
    // functions whose explicit parameters are propositions, applied to the hypotheses; computed only when a solver applies
    val hintInstances: List<org.arend.ext.concrete.expr.ConcreteExpression> by lazy { timed("hints", emptyList()) { lemmaHints(goal) } }
    if (Heuristic.CLOSE in heuristics) {
      val closing = timed("close", emptyList()) { ClosingGenerator(moduleLocation, closingMetaRefs, usingMeta = usingRef, solvers = equationSolvers, pmap = pmapRef, lemmaHints = { hintInstances }).generate(goal, currentProof) }
      // A goal that can be closed needs no other step
      if (closing.isNotEmpty()) { report(); return closing }
    }

    val steps = mutableListOf<ProofStep<ArendGoal>>()
    // What the fits compare against, computed once per goal rather than once per candidate
    val goalType = goal.expectedType.toString()
    val strippedGoal by lazy { ConclusionMatcher.strippedGoal(goal.expectedType) }
    val goalSubterms by lazy { ConclusionMatcher.SubtermIndex(ConclusionMatcher.goalSubterms(goal.expectedType)) }
    val goalHeads by lazy { ConclusionMatcher.goalHeads(goal.expectedType) }
    // A premise about other functions than the goal's cannot fit; the matcher is only run on the rest
    fun applyFit(premise: CallableDefinition): Int? = cachedFit(Triple("apply", goalType, premise)) {
      if (ConclusionMatcher.mayFit(premise, goalHeads)) ConclusionMatcher.applyScore(premise, goal.expectedType, strippedGoal) else null
    }
    fun reversedFit(premise: CallableDefinition): Int? = cachedFit(Triple("reversed", goalType, premise)) {
      if (applyFit(premise) == null && ConclusionMatcher.mayFit(premise, goalHeads)) ConclusionMatcher.reversedApplyScore(premise, goal.expectedType) else null
    }
    fun rewriteFit(premise: CallableDefinition): Int? = cachedFit(Triple("rewrite", goalType, premise)) {
      ConclusionMatcher.rewriteSideScores(premise, goalSubterms)?.let { (left, right) -> listOfNotNull(left, right).maxOrNull() }
    }
    // The library equations the goal may be rewritten with, for rewriting and for deciding what to unfold
    val equationCandidates by lazy { timed("retrieve equations") { rewriteRetrievers.flatMap { it.retrieve(goal) } } }
    val rewriteLemmas: Map<CallableDefinition, Double> by lazy {
      if (rewriteMetas == null) emptyMap() else {
        val candidates = equationCandidates
        timed("resolve equations ${candidates.size}") { resolvePremises(goal, candidates, fit = ::rewriteFit, memo = "rewrite") }
      }
    }
    // The library equations with a bare-parameter side about a function of the goal or of a hypothesis: `rewrite` cannot use them, `transport` can
    val goalFunctions by lazy { (EquationRetriever.functionNames(goal.expectedType) + goal.typechecker.context.values.flatMap { EquationRetriever.functionNames(it.type) }).toSet() }
    val transportCandidates by lazy { timed("retrieve transports") { rewriteRetrievers.flatMap { (it as? EquationRetriever)?.retrieve(goal, includeHypotheses = true) ?: it.retrieve(goal) } } }
    fun transportFit(premise: CallableDefinition): Int? = cachedFit(Triple("transport", goalType, premise)) {
      val (left, right) = RewriteGenerator.lemmaSides(premise) ?: return@cachedFit null
      val other = when {
        right is org.arend.core.expr.ReferenceExpression -> left
        left is org.arend.core.expr.ReferenceExpression -> right
        else -> return@cachedFit null
      }
      if (other is org.arend.core.expr.ReferenceExpression) return@cachedFit null
      // Not along idempotence, `x ∧ x = x`: it only duplicates the argument, and arend-lib never transports along it
      if (TransportGenerator.isIdempotence(other)) return@cachedFit null
      val mentioned = EquationRetriever.functionNames(other).count { it in goalFunctions }
      if (mentioned > 0) mentioned else null
    }
    val transportLemmas: Map<CallableDefinition, Double> by lazy {
      if (transportRefs == null) emptyMap() else timed("resolve transports ${transportCandidates.size}") { resolvePremises(goal, transportCandidates, fit = ::transportFit, memo = "transport") }
    }
    if (Heuristic.APPLY in heuristics) {
      val goalArity = AppGenerator.arity(goal.expectedType)
      val candidates = timed("retrieve") { retrievers.flatMap { it.retrieve(goal) } }
      val closes = { premise: CallableDefinition -> AppGenerator.subgoalCount(premise, goalArity) == 0 }
      val premises = timed("resolve ${candidates.size}") {
        resolvePremises(goal, candidates, fit = ::applyFit, closes = closes, penalizeGeneric = true, memo = "apply")
      }
      val inv = invRef
      // Equations that conclude the goal read backwards are applied as `inv L`
      val reversed = if (inv == null || RewriteGenerator.equationSides(goal.expectedType) == null) emptyMap() else timed("resolve reversed") {
        resolvePremises(goal, candidates, fit = ::reversedFit, closes = closes, penalizeGeneric = true, memo = "reversed").mapValues { it.value + REVERSED_COST }
      }
      val all = LinkedHashMap(premises).also { map -> reversed.forEach { (premise, cost) -> map.putIfAbsent(premise, cost) } }
      val problem = goal.toString()
      val rejected = rejectedPremises.getOrPut(problem) { HashSet() }
      val tried = all.keys.filter { it !in rejected }
      val applied = timed("apply ${tried.size}", emptyList()) { AppGenerator(tried, moduleLocation, all, reversed = reversed.keys, inv = inv).generate(goal, currentProof) }
      // Premises that yielded nothing for this statement are not tried on it again
      // A premise prints by its alias when it has one: `<=-transitive` as `<=∘`
      fun names(premise: CallableDefinition) = listOfNotNull(premise.ref.refName, (premise.ref as? org.arend.naming.reference.GlobalReferable)?.aliasName)
      val productive = applied.mapNotNullTo(HashSet()) { step -> tried.find { premise -> names(premise).any { name -> step.proof.toString().contains(name) } } }
      rejected += tried.filter { it !in productive }
      steps += applied
      // Premises of a class the goal's instance only converts to (`CancelMonoid.cancel_*-left` for `A : AddGroup`, whose
      // instance of `CancelMonoid` cannot be inferred) are applied with the converted instance, `{toGroup A}`
      if (conversions.isNotEmpty()) {
        val factory = goal.typechecker.factory
        val contextInstances = StepBuilder.context(goal).mapNotNull { (ref, binding) -> (binding.type.normalize(org.arend.ext.core.ops.NormalizationMode.WHNF) as? org.arend.core.expr.ClassCallExpression)?.definition?.let { ref to it } }
        for (conversion in conversions) for ((ref, instanceClass) in contextInstances) {
          if (!instanceClass.isSubClassOf(conversion.from)) continue
          val group = tried.filter { premise -> instanceClassOf(premise)?.let { conversion.to.isSubClassOf(it) && !instanceClass.isSubClassOf(it) } == true }
          if (group.isNotEmpty()) {
            val converted = factory.app(factory.ref(conversion.function.ref), true, factory.ref(ref))
            // The instance parameter is named after the class or `this`: given by its actual name
            steps += timed("convert ${group.size}", emptyList()) {
              group.groupBy { instanceParameterName(it) }.flatMap { (name, premises) ->
                if (name == null) emptyList() else AppGenerator(premises, moduleLocation, all, fixedImplicits = mapOf(name to converted)).generate(goal, currentProof)
              }
            }
          }
        }
      }
      val concat = concatRef
      if (concat != null && inv != null) steps += timed("path", emptyList()) { PathGenerator(moduleLocation, concat, inv, lemmas = rewriteLemmas.keys.toList(), lemmaCosts = rewriteLemmas).generate(goal, currentProof) }
      // Chains through a hypothesis function or a lemma with hypotheses, their arguments left as goals: `{?} <=∘ mon {?}`
      if (chainRefs.isNotEmpty() && System.getenv("AREND_PS_NO_INSTANCE_CHAINS") == null && goal.expectedType !is org.arend.core.expr.PiExpression && ConclusionMatcher.relationSides(goal.expectedType) != null) {
        val pool = if (RewriteGenerator.equationSides(goal.expectedType) != null) timed("resolve chain lemmas") { resolvePremises(goal, equationCandidates, memo = "hint") }
          else timed("resolve chain lemmas") { resolvePremises(goal, candidates, limit = Int.MAX_VALUE, memo = "fix") }
        steps += timed("instance chains", emptyList()) { InstanceChainGenerator(moduleLocation, chainRefs, inv, pool).generate(goal, currentProof) }
      }
    }
    if (Heuristic.TUPLE in heuristics) {
      steps += timed("tuple", emptyList()) { TupleGenerator(moduleLocation).generate(goal, currentProof) }
      steps += timed("new", emptyList()) { NewGenerator(moduleLocation).generate(goal, currentProof) }
    }
    if (Heuristic.UNFOLD in heuristics) {
      unfoldRef?.let { steps += timed("unfold", emptyList()) { UnfoldGenerator(moduleLocation, it, rewriteLemmas = rewriteLemmas.keys.toList()).generate(goal, currentProof) } }
    }
    if (Heuristic.INTRO in heuristics) {
      steps += timed("intro", emptyList()) { IntroGenerator(moduleLocation).generate(goal, currentProof) }
    }
    if (Heuristic.HYPOTHESIS in heuristics) {
      steps += timed("hypothesis", emptyList()) { HypothesisGenerator(moduleLocation, absurdRef).generate(goal, currentProof) }
    }
    if (Heuristic.INDUCTION in heuristics) {
      steps += timed("induction", emptyList()) { InductionGenerator(moduleLocation, rewriteMetas = rewriteMetas, chains = chainRefs, solvers = equationSolvers, lemmaHints = { hintInstances }).generate(goal, currentProof) }
    }
    if (Heuristic.EXT in heuristics) {
      extRef?.let { steps += timed("ext", emptyList()) { ExtGenerator(moduleLocation, it).generate(goal, currentProof) } }
    }
    if (Heuristic.CONGRUENCE in heuristics) {
      pmapRef?.let { steps += timed("congruence", emptyList()) { CongruenceGenerator(moduleLocation, it).generate(goal, currentProof) } }
    }
    if (Heuristic.CASE in heuristics) {
      val splitLemmas = if (splitRetrievers.isEmpty()) emptyList() else timed("retrieve splits", emptyList()) {
        resolvePremises(goal, splitRetrievers.flatMap { it.retrieve(goal) }, memo = "split").map { (definition, cost) -> definition to cost }
      }
      steps += timed("case", emptyList()) { CaseGenerator(moduleLocation, splitterRefs, mcasesRef, splitLemmas).generate(goal, currentProof) }
    }
    // Lemmas of a twin structure, applied with the instance converted: `AddMonoid.BigSum_suc {AddMonoid.fromMonoid A}`
    if (Heuristic.APPLY in heuristics) transferRetriever?.let { retriever ->
      val candidates = timed("retrieve transfers") { retriever.retrieve(goal) }
      if (candidates.isNotEmpty()) {
        // Their conclusions only compute to the goal's form: not fitted, typechecked
        val premises = timed("resolve transfers ${candidates.size}") { resolvePremises(goal, candidates, memo = "transfer") }
        val factory = goal.typechecker.factory
        val groups = candidates.mapNotNull { candidate -> retriever.instanceOf(candidate)?.let { it to candidate } }.groupBy({ it.first }, { it.second })
        if (debug) println("Transfer candidates for ${goal.expectedType}: ${candidates.map { it.name }}; resolved ${premises.keys.map { it.ref.refName }}")
        steps += timed("transfer", emptyList()) {
          groups.flatMap { (instance, group) ->
            val (conversion, ref) = instance
            val names = group.map { it.name.substringAfterLast('.') }.toSet()
            val defs = premises.filterKeys { it.ref.refName in names }
            if (defs.isEmpty()) emptyList() else AppGenerator(defs.keys.toList(), moduleLocation, defs, fixedImplicits = mapOf("this" to factory.app(factory.ref(conversion.function.ref), true, factory.ref(ref)))).generate(goal, currentProof)
          }
        }
      }
    }
    if (Heuristic.INJECTIVITY in heuristics && destructorRetrievers.isNotEmpty()) {
      pmapRef?.let { pmap ->
        val destructors = timed("retrieve destructors", emptyMap()) { resolvePremises(goal, destructorRetrievers.flatMap { it.retrieve(goal) }, memo = "destructor") }
        steps += timed("injectivity ${destructors.size}", emptyList()) { InjectivityGenerator(moduleLocation, pmap, destructors).generate(goal, currentProof) }
      }
    }
    if (Heuristic.TRANSPORT in heuristics) {
      transportRefs?.let { (transport, transportInv) ->
        val lemmas = transportLemmas
        steps += timed("transport ${lemmas.size}", emptyList()) { TransportGenerator(moduleLocation, transport, transportInv, lemmas.keys.toList(), lemmas).generate(goal, currentProof) }
      }
      // A relation lemma applied to the hypotheses and brought to the goal by equations, `transport2 (<=) {?} {?} (<=_+ <=-refl p)`:
      // its lemmas do not fit the goal, so every retrieved premise is resolved for it
      val relationGoal = goal.expectedType !is org.arend.core.expr.PiExpression && RewriteGenerator.equationSides(goal.expectedType) == null && ConclusionMatcher.relationSides(goal.expectedType) != null
      if (relationGoal) transport2Ref?.let { transport2 ->
        val pool = timed("resolve fixes") { resolvePremises(goal, retrievers.flatMap { it.retrieve(goal) }, limit = Int.MAX_VALUE, memo = "fix") }
        steps += timed("fix", emptyList()) { RelationFixGenerator(moduleLocation, transport2, pool).generate(goal, currentProof) }
      }
    }
    if (Heuristic.REWRITE in heuristics) {
      rewriteMetas?.let { metas ->
        val lemmas = rewriteLemmas
        steps += timed("rewrite ${lemmas.size}", emptyList()) { RewriteGenerator(moduleLocation, metas, lemmas.keys.toList(), lemmas).generate(goal, currentProof) }
      }
    }
    report()
    if (StepBuilder.timing) steps.sortedBy { it.score }.forEach { println("Step %.2f: %s".format(it.score, it.proof.toString().replace("\n", " "))) }
    return steps
  }
}
