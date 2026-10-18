package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.CMP
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.Referable
import org.arend.typechecking.implicitargs.equations.DummyEquations
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Transports a relation along an equation at one argument, `transport (n mod m <=) (divModProp n m) {?}`,
 * where arend-lib uses `transport`/`transportInv` rather than `rewrite` (`mod<=left`, `div_*<=id`,
 * `<=_+-cancel-left`, `negative_<=-conv`, `Inv_negative`):
 * - with a hypothesis `p : a = b` whose side is an argument of the goal's relation that also occurs
 *   elsewhere in the goal, so that rewriting would change both occurrences (`n mod m <= n` along `_ = n`);
 * - with a library equation one side of which is a bare parameter (`divModProp n m : m * (n div m) + n mod m = n`),
 *   which `rewrite` cannot use, applied to the variables of the context its explicit parameters take.
 * The motive replaces the argument by a bound variable: `\lam z => n mod m <= z`.
 */
class TransportGenerator(
  private val moduleLocation: ModuleLocation,
  private val transport: ArendRef,
  private val transportInv: ArendRef,
  /** Library equations with a bare-parameter side, ranked for the goal, with their costs. */
  private val lemmas: List<CallableDefinition> = emptyList(),
  private val lemmaCosts: Map<CallableDefinition, Double> = emptyMap(),
) : ProofStepGenerator<ArendGoal> {
  companion object {
    /** Whether [side] is one operation applied to copies of one variable, as `x ∧ x` of `meet-idemp`. */
    fun isIdempotence(side: Expression): Boolean {
      var current: Expression = side
      val arguments = mutableListOf<Expression>()
      while (current is org.arend.core.expr.AppExpression) { arguments.add(current.argument); current = current.function }
      // A class operation's own argument is its instance, not an operand
      if (current !is org.arend.core.expr.FieldCallExpression) (current as? org.arend.core.expr.DefCallExpression)?.defCallArguments?.let { arguments.addAll(it) }
      val variables = arguments.filterIsInstance<org.arend.core.expr.ReferenceExpression>()
      return arguments.size >= 2 && variables.size == arguments.size && variables.map { it.binding }.toSet().size == 1
    }

    const val HYPOTHESIS_COST = 0.9
    const val LEMMA_COST = 1.6
    const val MAX_ARGUMENT_CHOICES = 4
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    val type = goal.expectedType
    // Equations are rewritten, not transported; a goal with parameters is introduced first
    if (type is PiExpression || RewriteGenerator.equationSides(type) != null) return emptyList()
    val (left, right) = ConclusionMatcher.relationSides(type) ?: return emptyList()
    val context = StepBuilder.context(goal)
    val contextMap = context.associate { it.second to it.first }
    val subterms = ConclusionMatcher.subterms(type)
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    fun same(a: Expression, b: Expression) = CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, a, b, null, null)
    fun add(term: ConcreteExpression, cost: Double) { StepBuilder.build(goal, currentProof, term, cost, moduleLocation)?.let { steps.add(it) } }

    for (argument in listOf(left, right)) {
      val z = factory.local("z")
      val motive = factory.lam(listOf(factory.param(true, z)), CoreToConcrete.convert(type, contextMap, factory, java.util.IdentityHashMap<Expression, ConcreteExpression>().apply { put(argument, factory.ref(z)) }) ?: continue)
      fun step(meta: ArendRef, equation: ConcreteExpression, cost: Double) = add(factory.app(factory.ref(meta), true, motive, equation, factory.goal()), cost)
      // A hypothesis whose side is the argument, when that side also occurs elsewhere in the goal
      val occursElsewhere = subterms.count { same(it, argument) } >= 2
      if (occursElsewhere) {
        for ((p, binding) in context) {
          val (a, b) = RewriteGenerator.equationSides(binding.type) ?: continue
          if (same(b, argument)) step(transport, factory.ref(p), HYPOTHESIS_COST)
          if (same(a, argument)) step(transportInv, factory.ref(p), HYPOTHESIS_COST)
        }
      }
      // A library equation with a bare-parameter side, applied to variables of the context
      for (lemma in lemmas) {
        val (l, r) = RewriteGenerator.lemmaSides(lemma) ?: continue
        val parameters = explicitParameters(lemma) ?: continue
        val bareRight = r is ReferenceExpression && parameters.any { it == r.binding } || r is ReferenceExpression && r.binding !in contextMap
        val bareLeft = l is ReferenceExpression && parameters.any { it == l.binding } || l is ReferenceExpression && l.binding !in contextMap
        if (!bareRight && !bareLeft) continue
        val choices = parameters.map { parameter -> context.filter { (_, binding) -> sameKind(parameter.type, binding.type) }.map { it.first } }
        if (choices.any { it.isEmpty() }) continue
        val cost = (lemmaCosts[lemma] ?: LEMMA_COST)
        for (args in combinations(choices).take(MAX_ARGUMENT_CHOICES)) {
          val equation = factory.app(factory.ref(lemma.ref), true, args.map { factory.ref(it) })
          if (bareRight) step(transport, equation, cost)
          if (bareLeft) step(transportInv, equation, cost)
        }
      }
    }
    return steps
  }

  private fun explicitParameters(definition: CallableDefinition): List<DependentLink>? = when (definition) {
    is FunctionDefinition -> DependentLink.Helper.toList(definition.parameters).filter { it.isExplicit }
    is ClassField -> generateSequence(definition.type.codomain) { (it as? PiExpression)?.codomain }
      .filterIsInstance<PiExpression>().flatMap { DependentLink.Helper.toList(it.parameters) }.filter { it.isExplicit }.toList()
    else -> null
  }

  private fun sameKind(expected: Expression, actual: Expression): Boolean {
    val head = PremiseRetriever.head(expected) ?: return false
    return PremiseRetriever.head(actual) == head
  }

  private fun <T> combinations(choices: List<List<T>>): Sequence<List<T>> =
    if (choices.isEmpty()) sequenceOf(emptyList()) else sequence {
      for (first in choices[0]) for (rest in combinations(choices.drop(1))) yield(listOf(first) + rest)
    }
}
