package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.core.ops.CMP
import org.arend.typechecking.implicitargs.equations.DummyEquations
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.Referable
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Chains through a relation that still has to be instantiated: a hypothesis that is a function,
 * `mon : \Pi (n : Nat) -> suc (f n) <= f (suc n)`, or a library lemma with hypotheses of its own,
 * `mod_< : n < m -> n mod m = n`, whose conclusion ends where the goal's relation starts or ends.
 * Its hypotheses are left as goals, `{?} *> inv (mod_< {?})`, since the chain fixes the instance's implicit
 * arguments and they are proved afterwards (`suc<suc p`); its elements are variables of the context, `{?} <=∘ mon n`.
 * arend-lib: `<=-transitive (suc<=suc IH) (mon n)` (`monotone-diagonal`),
 * `pmap suc (mod_< p) *> inv (mod_< (suc<suc p))` (`mod_suc`), `<=_*-left b p <=∘ <=_*-right c q` (`<=_*`).
 *
 * Applies to a binary relation goal with a transitivity operator; an end is used only where a side of its
 * conclusion matches an end of the goal beyond a bare variable, and a lemma only with at most
 * [MAX_PARAMETERS] explicit parameters, all of them propositions.
 */
class InstanceChainGenerator(
  private val moduleLocation: ModuleLocation,
  /** Transitivity operators: `<=-transitive` (`<=∘`) and `*>`. */
  private val chains: List<ArendRef>,
  private val inv: ArendRef?,
  /** Library lemmas the goal may chain through, with their costs. */
  private val lemmas: Map<CallableDefinition, Double>,
  private val cost: Double = 1.0,
) : ProofStepGenerator<ArendGoal> {
  companion object {
    const val MAX_PARAMETERS = 2
    const val MAX_LEMMAS = 8
    const val MAX_ARGUMENT_LISTS = 4
    /** Added to [cost] for a library lemma, which is less certain than a hypothesis. */
    const val LEMMA_EXTRA_COST = 0.4
  }

  private val debug = System.getProperty("proofsearch.debug") == "true"

  /** An end of a chain: [vars] are the pattern variables of [conclusion] (the function's parameters), the rest is rigid. */
  private class End(val expression: ConcreteExpression, val conclusion: Expression, val vars: Set<Binding>, val cost: Double, val holes: Int)

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val type = goal.expectedType
    if (type is PiExpression || chains.isEmpty()) return emptyList()
    val (left, right) = ConclusionMatcher.relationSides(type) ?: run { if (debug) println("Instance chains: no relation sides for $type"); return emptyList() }
    val key = PremiseRetriever.headKey(type) ?: return emptyList()
    val isEquation = RewriteGenerator.equationSides(type) != null
    val factory = goal.typechecker.factory
    val ends = mutableListOf<End>()
    val context = StepBuilder.context(goal)
    /**
     * The argument lists for [parameters]: a proposition is left as a goal (`{?}`, a hole is not an inference variable,
     * so nothing it stands in would be inferred, but the conclusion does not depend on a proof), an element is each
     * context variable of its type (`mon n`); null when an element has none.
     */
    fun arguments(parameters: List<DependentLink>): List<Pair<List<ConcreteExpression>, Int>>? {
      val choices = parameters.map { parameter ->
        if (LemmaHints.isProposition(parameter.type)) listOf(factory.goal() to 1)
        else context.filter { (_, binding) -> CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, binding.type, parameter.type, null, null) }
          .map { factory.ref(it.first) to 0 }.ifEmpty { return null }
      }
      return choices.fold(listOf(emptyList<ConcreteExpression>() to 0)) { acc, options -> acc.flatMap { (prefix, holes) -> options.map { (arg, hole) -> (prefix + arg) to (holes + hole) } } }
        .take(MAX_ARGUMENT_LISTS)
    }
    // Hypotheses that are functions into the goal's relation
    for ((ref, binding) in context) {
      // Parameters are peeled until the goal's relation shows: it is not unfolded further (Nat's `<=` is `Not (<)`, a function type)
      var conclusion: Expression = binding.type
      val parameters = mutableListOf<DependentLink>()
      val binders = HashSet<Binding>()
      while (parameters.size <= MAX_PARAMETERS && !(parameters.isNotEmpty() && PremiseRetriever.headKey(conclusion) == key)) {
        val pi = conclusion.normalize(NormalizationMode.WHNF) as? PiExpression ?: break
        val all = DependentLink.Helper.toList(pi.parameters)
        binders.addAll(all)
        parameters += all.filter { it.isExplicit }
        conclusion = pi.codomain
      }
      if (parameters.isEmpty() || parameters.size > MAX_PARAMETERS || PremiseRetriever.headKey(conclusion) != key) continue
      for ((args, holes) in arguments(parameters) ?: continue) ends.add(End(factory.app(factory.ref(ref), true, args), conclusion, binders, cost, holes))
    }
    // Library lemmas with hypotheses, concluding the goal's relation
    val candidates = lemmas.entries.mapNotNull { (lemma, lemmaCost) ->
      val explicit = RelationFixGenerator.explicitParameters(lemma)
      if (explicit.isEmpty() || explicit.size > MAX_PARAMETERS || !explicit.all { LemmaHints.isProposition(it.type) }) return@mapNotNull null
      val conclusion = ConclusionMatcher.conclusion(lemma) ?: return@mapNotNull null
      if (PremiseRetriever.headKey(conclusion) != key) return@mapNotNull null
      End(factory.app(factory.ref(lemma.ref), true, List(explicit.size) { factory.goal() }), conclusion, RelationFixGenerator.allParameters(lemma).toSet(), lemmaCost + LEMMA_EXTRA_COST, explicit.size)
    }.sortedBy { it.cost }.take(MAX_LEMMAS)
    ends.addAll(candidates)
    if (debug) println("Instance chains for $type: ${ends.map { "${it.expression} : ${it.conclusion}" }} with ${chains.map { it.refName }}")
    if (ends.isEmpty()) return emptyList()

    val steps = mutableListOf<ProofStep<ArendGoal>>()
    for (end in ends) {
      val (a, b) = ConclusionMatcher.relationSides(end.conclusion) ?: continue
      fun matches(side: Expression, goalEnd: Expression) = side !is ReferenceExpression && (ConclusionMatcher.match(side, goalEnd, end.vars) ?: 0) >= 1
      val stepCost = end.cost + end.holes * AppGenerator.SUBGOAL_COST
      val flipped = inv?.let { factory.app(factory.ref(it), true, end.expression) }
      for (chain in chains) {
        fun add(first: ConcreteExpression, second: ConcreteExpression) {
          StepBuilder.build(goal, currentProof, factory.app(factory.ref(chain), true, first, second), stepCost, moduleLocation)?.let { steps.add(it) }
        }
        if (matches(a, left)) add(end.expression, factory.goal())
        if (matches(b, right)) add(factory.goal(), end.expression)
        if (isEquation && flipped != null) {
          if (matches(b, left)) add(flipped, factory.goal())
          if (matches(a, right)) add(factory.goal(), flipped)
        }
      }
    }
    return steps
  }
}
