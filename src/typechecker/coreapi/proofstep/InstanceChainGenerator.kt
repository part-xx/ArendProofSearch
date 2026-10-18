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
    const val MAX_LEMMAS = 16
    const val MAX_ARGUMENT_LISTS = 4
    const val MAX_CHOICES = 2
    /** Added to [cost] for a library lemma, which is less certain than a hypothesis. */
    const val LEMMA_EXTRA_COST = 0.4

    /** An argument list: the expressions, how many are holes, and which element parameters got which context variable. */
    class Arguments(val expressions: List<ConcreteExpression>, val holes: Int, val elements: List<Pair<DependentLink, Binding>>)
    private class Option(val expression: ConcreteExpression, val hole: Int, val element: Pair<DependentLink, Binding>?)

    /**
     * The argument lists for [parameters] over [goal]'s context: a hypothesis parameter (by [isHypothesis]) is left as
     * a goal (`{?}`, a hole is not an inference variable, so nothing it stands in would be inferred, but the conclusion
     * does not depend on a proof) and also given each context hypothesis shaped like it (`<=_*_positive-right {?} k<=l`,
     * `div_< n<m`); an element is each context variable of its type (`mon n`, `divModProp n m`); null when an element has none.
     */
    fun argumentLists(goal: ArendGoal, parameters: List<DependentLink>, vars: Set<Binding>, isHypothesis: (DependentLink) -> Boolean = { LemmaHints.isProposition(it.type) }): List<Arguments>? {
      val factory = goal.typechecker.factory
      val context = StepBuilder.context(goal)
      val choices = parameters.map { parameter ->
        if (isHypothesis(parameter)) {
          val hypotheses = context.filter { (_, binding) -> (ConclusionMatcher.match(parameter.type, binding.type, vars) ?: -1) >= 1 }.map { Option(factory.ref(it.first), 0, null) }
          listOf(Option(factory.goal(), 1, null)) + hypotheses.take(MAX_CHOICES)
        } else context.filter { (_, binding) -> CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, binding.type, parameter.type, null, null) }
          .map { Option(factory.ref(it.first), 0, parameter to it.second) }.ifEmpty { return null }
      }
      return choices.fold(listOf(Arguments(emptyList(), 0, emptyList()))) { acc, options ->
        acc.flatMap { prefix -> options.map { o -> Arguments(prefix.expressions + o.expression, prefix.holes + o.hole, prefix.elements + listOfNotNull(o.element)) } }
      }.take(MAX_ARGUMENT_LISTS)
    }

    /** [conclusion] with the element parameters replaced by the context variables chosen. */
    fun instantiate(conclusion: Expression, elements: List<Pair<DependentLink, Binding>>): Expression {
      if (elements.isEmpty()) return conclusion
      val substitution = org.arend.core.subst.ExprSubstitution()
      for ((parameter, binding) in elements) substitution.add(parameter, ReferenceExpression(binding))
      return conclusion.subst(substitution)
    }
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
      for (list in argumentLists(goal, parameters, binders) ?: continue) {
        ends.add(End(factory.app(factory.ref(ref), true, list.expressions), instantiate(conclusion, list.elements), binders - list.elements.map { it.first }.toSet(), cost, list.holes))
      }
    }
    // Library lemmas with hypotheses, concluding the goal's relation; those about a function of the goal first
    // (`<=_*_positive-right` for `n * k <= m * l`), as hundreds conclude an order
    val relationName = PremiseRetriever.headName(type)
    val goalFunctions = EquationRetriever.functionNames(type).filter { it != relationName }.toSet()
    val candidates = lemmas.entries.mapNotNull { (lemma, lemmaCost) ->
      // Elements are taken from the context, `divModProp n m` (`mod_<`): the instantiated conclusion then ends at `n` itself
      val explicit = RelationFixGenerator.explicitParameters(lemma)
      if (explicit.isEmpty() || explicit.size > MAX_PARAMETERS) return@mapNotNull null
      val conclusion = ConclusionMatcher.conclusion(lemma) ?: return@mapNotNull null
      if (PremiseRetriever.headKey(conclusion) != key) return@mapNotNull null
      val about = EquationRetriever.functionNames(conclusion).any { it in goalFunctions }
      // The pattern's variables: the lemma's parameters and whatever else is free in its conclusion (a class's `this`
      // is not always among the parameters), minus the goal's own context
      val contextBindings = context.map { it.second }.toSet()
      val vars = RelationFixGenerator.allParameters(lemma).toSet<Binding>() + org.arend.core.expr.visitor.FreeVariablesCollector.getFreeVariables(conclusion).filter { it !in contextBindings }
      val lists = argumentLists(goal, explicit, vars) { RelationFixGenerator.isHypothesisParameter(lemma, it) } ?: return@mapNotNull null
      // Ranked: about the goal's operations first, then those a hypothesis instantiates, then by cost
      val instantiated = lists.any { it.holes < explicit.size }
      if (debug) println("Instance chain lemma ${lemma.ref.refName} (${lemma.ref.location?.modulePath}): ${lists.size} argument lists, about $about")
      // A lemma fully instantiated from the context (`divModProp n m`) is as definite as a hypothesis: no extra cost
      Triple(lists.map { list -> End(factory.app(factory.ref(lemma.ref), true, list.expressions), instantiate(conclusion, list.elements), vars - list.elements.map { it.first }.toSet(), lemmaCost + (if (list.holes == 0) 0.0 else LEMMA_EXTRA_COST), list.holes) }, about to instantiated, lemmaCost)
    }.sortedWith(compareBy({ !it.second.first }, { !it.second.second }, { it.third })).take(MAX_LEMMAS).flatMap { it.first }
    ends.addAll(candidates)
    if (debug) println("Instance chains for $type: ${ends.map { "${it.expression} : ${it.conclusion}" }} with ${chains.map { it.refName }}")
    if (ends.isEmpty()) return emptyList()

    val steps = mutableListOf<ProofStep<ArendGoal>>()
    for (end in ends) {
      val (a, b) = ConclusionMatcher.relationSides(end.conclusion) ?: continue
      fun matches(side: Expression, goalEnd: Expression) =
        if (side is ReferenceExpression) side.binding !in end.vars && goalEnd is ReferenceExpression && goalEnd.binding == side.binding
        else (ConclusionMatcher.match(side, goalEnd, end.vars) ?: 0) >= 1
      val stepCost = end.cost + end.holes * AppGenerator.SUBGOAL_COST
      val flipped = inv?.let { factory.app(factory.ref(it), true, end.expression) }
      for (chain in chains) {
        /**
         * The chain with its middle term written, `{?} *> {_} {_} {m * (n div m) + n mod m} {_} divModProp n m`: the whole
         * proof is typechecked again as a unit, where a meta filling the hole (`rewrite (div_< {?})`) runs before the
         * middle is inferred from the other end and fails. Both operators take it as their third implicit argument.
         */
        fun add(first: ConcreteExpression, second: ConcreteExpression, middle: Expression) {
          val mid = CoreToConcrete.convert(middle, goal)
          val term = if (mid == null) factory.app(factory.ref(chain), true, first, second)
            else factory.app(factory.ref(chain), listOf(factory.arg(factory.hole(), false), factory.arg(factory.hole(), false), factory.arg(mid, false), factory.arg(factory.hole(), false), factory.arg(first, true), factory.arg(second, true)))
          StepBuilder.build(goal, currentProof, term, stepCost, moduleLocation)?.let { steps.add(it) }
        }
        if (matches(a, left)) add(end.expression, factory.goal(), b)
        if (matches(b, right)) add(factory.goal(), end.expression, a)
        if (isEquation && flipped != null) {
          if (matches(b, left)) add(flipped, factory.goal(), a)
          if (matches(a, right)) add(factory.goal(), flipped, b)
        }
      }
    }
    return steps
  }
}
