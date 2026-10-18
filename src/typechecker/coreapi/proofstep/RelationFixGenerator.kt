package typechecker.coreapi.proofstep

import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.AppExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * A relation lemma applied to the hypotheses, brought to the goal by an equation at each argument:
 * `transport (<= _) zro-left $ <=_+ a>=0 b>=0` is arend-lib's `<=_+-positive`, and `transport2 (<=) e1 e2 (<=_+ <=-refl p)`
 * its `<=_+-cancel-left`, `negative_<=`, `div_*<=id`: the lemma concludes the goal's relation between sides
 * that only equal the goal's in the theory (`0 + 0 = 0`, `negative x + (x + y) = y`), which the solvers then close.
 * Here both equations are left as goals, `transport2 (<=) {?} {?} (<=_+ a>=0 b>=0)`, so the instance's own
 * type has to determine them: its arguments are hypotheses of the context, or lemmas without any parameters.
 *
 * Applies when the goal is a binary relation other than equality and the lemma concludes the same
 * relation, takes only hypotheses of that relation, at least one of them a hypothesis of the context when
 * there is any, and mentions a function of the goal or of a hypothesis (`+` of `p : x + y <= x + z`).
 */
class RelationFixGenerator(
  private val moduleLocation: ModuleLocation,
  private val transport2: ArendRef,
  /** The retrieved premises with their costs; the relation lemmas and the closed lemmas are picked from them. */
  private val premises: Map<CallableDefinition, Double>,
  private val extraCost: Double = EXTRA_COST,
) : ProofStepGenerator<ArendGoal> {
  companion object {
    /** Added to the lemma's cost: the step leaves two equations to prove. */
    const val EXTRA_COST = 0.6
    const val MAX_LEMMAS = 6
    const val MAX_CHOICES = 3
    const val MAX_INSTANCES_PER_LEMMA = 6

    /** The explicit parameters of a lemma or a class field. */
    fun explicitParameters(definition: CallableDefinition): List<DependentLink> = allParameters(definition).filter { it.isExplicit }

    /**
     * Whether [parameter] of [lemma] is a hypothesis rather than an element: nothing after it depends on it, in
     * particular not the conclusion (`n<m : n < m` of `div_<`, whose conclusion `n div m = 0` mentions `n` and `m`
     * but not the proof). Propositions count regardless.
     */
    fun isHypothesisParameter(lemma: CallableDefinition, parameter: DependentLink): Boolean {
      if (LemmaHints.isProposition(parameter.type)) return true
      val conclusion = ConclusionMatcher.conclusion(lemma) ?: return false
      if (StepBuilder.occurs(parameter, conclusion)) return false
      val all = allParameters(lemma)
      val index = all.indexOf(parameter)
      return all.drop(index + 1).none { StepBuilder.occurs(parameter, it.type) }
    }

    /** All parameters of a lemma or a class field, implicit ones included. */
    fun allParameters(definition: CallableDefinition): List<DependentLink> = when (definition) {
      is FunctionDefinition -> DependentLink.Helper.toList(definition.parameters)
      is ClassField -> generateSequence(definition.type.codomain) { (it as? PiExpression)?.codomain }
        .filterIsInstance<PiExpression>().flatMap { DependentLink.Helper.toList(it.parameters) }.toList()
      else -> emptyList()
    }

    /** The definition at the head of the relation [type] (`<=` of a poset, Nat's `<=`), or null. */
    fun relationDefinition(type: Expression): DefCallExpression? {
      var current: Expression = type.normalize(NormalizationMode.WHNF)
      while (current is AppExpression) current = current.function
      return current as? DefCallExpression
    }
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val type = goal.expectedType
    if (type is PiExpression || RewriteGenerator.equationSides(type) != null) return emptyList()
    ConclusionMatcher.relationSides(type) ?: return emptyList()
    val relation = relationDefinition(type) ?: return emptyList()
    val key = PremiseRetriever.headKey(type) ?: return emptyList()
    val factory = goal.typechecker.factory
    val context = StepBuilder.context(goal)
    val hypotheses = context.filter { (_, binding) -> PremiseRetriever.headKey(binding.type) == key }.map { factory.ref(it.first) }
    // Closed lemmas only without parameters at all: `<=-refl {x}` with nothing determining `x` leaves the equations' sides uninferred
    val closed = premises.keys.filter { allParameters(it).isEmpty() && ConclusionMatcher.conclusion(it)?.let { c -> PremiseRetriever.headKey(c) } == key }
      .map { factory.ref(it.ref) }
    // The functions besides the relation itself: `+` of `p : x + y <= x + z`, not `<=`
    val relationName = relation.definition.name
    fun functions(expression: Expression) = EquationRetriever.functionNames(expression).filter { it != relationName }
    val mentioned = (functions(type) + context.flatMap { functions(it.second.type) }).toSet()
    val lemmas = premises.entries.filter { (lemma, _) ->
      val parameters = explicitParameters(lemma)
      val conclusion = ConclusionMatcher.conclusion(lemma) ?: return@filter false
      parameters.isNotEmpty() && parameters.size <= LemmaHints.MAX_PARAMETERS &&
        parameters.all { PremiseRetriever.headKey(it.type) == key } &&
        PremiseRetriever.headKey(conclusion) == key &&
        functions(conclusion).any { it in mentioned }
    }.sortedBy { it.value }.take(MAX_LEMMAS)
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    val relationRef = factory.ref(relation.definition.ref)
    for ((lemma, cost) in lemmas) {
      val arity = explicitParameters(lemma).size
      val choices = List(arity) { (hypotheses + closed).take(MAX_CHOICES) }
      val instances = combinations(choices)
        // One of the arguments is a hypothesis when there is one: the lemma is applied to the context, not stated from nothing
        .filter { args -> hypotheses.isEmpty() || args.any { it in hypotheses } }
        .take(MAX_INSTANCES_PER_LEMMA)
      for (args in instances) {
        val instance = factory.app(factory.ref(lemma.ref), true, args)
        val term = factory.app(factory.ref(transport2), true, relationRef, factory.goal(), factory.goal(), instance)
        StepBuilder.build(goal, currentProof, term, cost + extraCost, moduleLocation)?.let { steps.add(it) }
      }
    }
    return steps
  }

  private fun <T> combinations(choices: List<List<T>>): List<List<T>> =
    choices.fold(listOf(emptyList())) { acc, options -> acc.flatMap { prefix -> options.map { prefix + it } } }
}
