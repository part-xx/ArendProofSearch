package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.core.ops.CMP
import org.arend.typechecking.implicitargs.equations.DummyEquations
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.Referable
import typechecker.coreapi.ArendGoal

/**
 * Lemma instances for a solver's hints: arend-lib gives its equation solvers not only the hypotheses but
 * lemmas applied to them, `equation.monoid {pow-comm p, pow-comm1 (inv p)}` (`pow-comm`),
 * `equation {usingOnly (finv-right xi, finv-right x+1i, ...)}` (`finv-diff`). An instance is a lemma
 * whose explicit parameters are all propositions, each given a hypothesis of the context that is shaped
 * like it (an equation also reversed, `inv p`); lemmas asking for elements are not guessed at.
 */
object LemmaHints {
  /** At most this many instances are offered for one goal. */
  const val MAX_INSTANCES = 6
  /** At most this many explicit parameters an instantiated lemma has. */
  const val MAX_PARAMETERS = 2
  /** At most this many hypotheses are tried for one parameter. */
  const val MAX_CHOICES = 3
  /** The solver is also tried with every ordered pair of the best this many instances. */
  const val MAX_PAIRED_INSTANCES = 4
  /** The score of a hypothesis applied to an element, above lemma instances: it is the context itself, not a guess from the library. */
  const val HYPOTHESIS_INSTANCE_SCORE = 10

  private class Argument(val expression: ConcreteExpression, val score: Int)

  /** Whether [type] is a proposition a hypothesis may state: an equation, or a type of sort `\Prop`. */
  fun isProposition(type: Expression): Boolean =
    RewriteGenerator.equationSides(type) != null || type.sortOfType?.isProp == true

  /**
   * The explicit parameters of [lemma] if there are 1 to [MAX_PARAMETERS] of them, all propositions, and the lemma
   * concludes an equation (`IsCentral_pow xc` concludes a function into equations: no hint); null otherwise.
   */
  fun propositionParameters(lemma: CallableDefinition): List<DependentLink>? {
    val explicit = RelationFixGenerator.explicitParameters(lemma)
    if (explicit.isEmpty() || explicit.size > MAX_PARAMETERS || !explicit.all { isProposition(it.type) }) return null
    val conclusion = when (lemma) {
      is FunctionDefinition -> lemma.resultType
      is org.arend.core.definition.ClassField -> generateSequence(lemma.type.codomain) { (it as? PiExpression)?.codomain }.last()
      else -> null
    } ?: return null
    if (RewriteGenerator.equationSides(conclusion) == null) return null
    return explicit
  }

  /** Whether the pattern [side] of a parameter matches the hypothesis side [target]: a bare parameter matches anything. */
  private fun sideMatches(side: Expression, target: Expression): Int? =
    if (side is ReferenceExpression) 0 else ConclusionMatcher.match(side, target)

  /**
   * The instances of [lemmas] whose explicit parameters are all given hypotheses of [goal]'s context,
   * best-matching first: `pow-comm1 p`, `pow-comm1 (inv p)`, `nonZero_* xi x+1i`.
   */
  fun instances(goal: ArendGoal, lemmas: Collection<CallableDefinition>, inv: ArendRef?): List<ConcreteExpression> {
    val factory = goal.typechecker.factory
    val hypotheses: List<Pair<Referable, Binding>> = StepBuilder.context(goal).filter { (_, binding) -> isProposition(binding.type) }
    if (hypotheses.isEmpty()) return emptyList()
    val result = mutableListOf<Pair<ConcreteExpression, Int>>()
    for (lemma in lemmas) {
      val parameters = propositionParameters(lemma) ?: continue
      val choices = parameters.map { parameter ->
        val sides = RewriteGenerator.equationSides(parameter.type)
        hypotheses.flatMap { (ref, binding) ->
          val direct = ConclusionMatcher.match(parameter.type, binding.type)?.let { Argument(factory.ref(ref), it) }
          // An equation hypothesis also read backwards, `pow-comm1 (inv p)`
          val reversed = if (inv == null || sides == null) null else RewriteGenerator.equationSides(binding.type)?.let { (left, right) ->
            val leftScore = sideMatches(sides.first, right) ?: return@let null
            val rightScore = sideMatches(sides.second, left) ?: return@let null
            Argument(factory.app(factory.ref(inv), true, factory.ref(ref)), leftScore + rightScore)
          }
          listOfNotNull(direct, reversed)
        }.sortedByDescending { it.score }.take(MAX_CHOICES)
      }
      if (choices.any { it.isEmpty() }) continue
      for (arguments in combinations(choices)) {
        result.add(factory.app(factory.ref(lemma.ref), true, arguments.map { it.expression }) to arguments.sumOf { it.score })
      }
    }
    result += hypothesisInstances(goal, hypotheses)
    return result.sortedByDescending { it.second }.map { it.first }.distinctBy { it.toString() }.take(MAX_INSTANCES)
  }

  /**
   * The groups of [instances] a solver is tried with: each alone, then each ordered pair of the best few
   * (the solver rewrites with its hints in order: `IsCentral_*` needs `yc z` before `xc z`), then all of them.
   */
  fun groups(instances: List<ConcreteExpression>): List<List<ConcreteExpression>> {
    val singles = instances.map { listOf(it) }
    val paired = instances.take(MAX_PAIRED_INSTANCES)
    val pairs = paired.flatMap { a -> paired.filter { it !== a }.map { b -> listOf(a, b) } }
    val all = if (instances.size > 2) listOf(instances) else emptyList()
    return singles + pairs + all
  }

  /**
   * Hypotheses that are functions from the carrier of the goal's equation into equations, `xc : IsCentral x`, that is
   * `\Pi (z : E) -> x * z = z * x`, applied to the carrier's elements in the context (`IsCentral_*`: `xc z`, `yc z`).
   */
  private fun hypothesisInstances(goal: ArendGoal, hypotheses: List<Pair<Referable, Binding>>): List<Pair<ConcreteExpression, Int>> {
    val factory = goal.typechecker.factory
    val (left, _) = RewriteGenerator.equationSides(goal.expectedType) ?: return emptyList()
    val carrier = RewriteGenerator.equationType(goal.expectedType) ?: left.type ?: return emptyList()
    fun isCarrier(type: Expression?) = type != null && CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, type, carrier, null, null)
    if (StepBuilder.context(goal).none { (_, binding) -> isCarrier(binding.type) }) return emptyList()
    val result = mutableListOf<Pair<ConcreteExpression, Int>>()
    for ((ref, binding) in hypotheses) {
      val parameters = mutableListOf<DependentLink>()
      var type = StepBuilder.unfold(binding.type)
      while (type is PiExpression) {
        parameters += DependentLink.Helper.toList(type.parameters)
        type = StepBuilder.unfold(type.codomain)
      }
      if (parameters.isEmpty() || parameters.size > MAX_PARAMETERS || !parameters.all { it.isExplicit && isCarrier(it.type) }) continue
      if (RewriteGenerator.equationSides(type) == null) continue
      // Applied to the other elements: `xc : IsCentral x` to `z`, not to `x` itself
      val others = StepBuilder.context(goal).filter { (_, other) -> isCarrier(other.type) && !StepBuilder.occurs(other, binding.type) }.map { factory.ref(it.first) }
      for (arguments in combinations(parameters.map { others })) {
        result.add(factory.app(factory.ref(ref), true, arguments) to HYPOTHESIS_INSTANCE_SCORE)
      }
    }
    return result
  }

  private fun <T> combinations(choices: List<List<T>>): List<List<T>> =
    choices.fold(listOf(emptyList())) { acc, options -> acc.flatMap { prefix -> options.map { prefix + it } } }
}
