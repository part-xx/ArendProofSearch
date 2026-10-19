package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.Expression
import org.arend.core.expr.FunCallExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.VoidExpressionVisitor
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.term.concrete.BaseConcreteExpressionVisitor
import org.arend.term.concrete.Concrete
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof

/**
 * Induction: the recursive call, as in `| suc m => -'+` or `| :: a l => pmap suc length_++`.
 *
 * The definition being proved is applied like any premise, but only inside a `\case \elim x`
 * branch, and only when the call decreases: an argument for an eliminated parameter is a variable
 * bound strictly inside that branch's constructor pattern, or the parameter itself. That is a structural recursion Arend's termination checker accepts, once the
 * enclosing `\case \elim` of the parameters is written as the lemma's `\elim` clauses
 * ([ArendProof.toSource]); Arend does not check termination through `\case` itself.
 */
class InductionGenerator(
  private val moduleLocation: ModuleLocation,
  private val cost: Double = 1.0,
  /** With the rewrite metas, an equation being proved is also rewritten with, as in `| suc m => rewrite pow_+ *-assoc`. */
  private val rewriteMetas: RewriteMetas? = null,
  /**
   * Transitivity operators (`<=∘`, `*>`): a relation being proved is also reached by a chain starting or
   * ending with the induction hypothesis, `Big_<=_join1 i <=∘ join-right`, `-'<=id <=∘ ...`, `<=-transitive (suc<=suc IH) (mon n)`.
   */
  private val chains: List<ArendRef> = emptyList(),
  /** arend-lib's specialized equation solvers: an equation being proved is also given to the solver of its class with the hypothesis as a hint, `equation.monoid {p, pow-comm1 p}`. */
  private val solvers: List<ClosingGenerator.Solver> = emptyList(),
  /** Lemma instances hinted besides the induction hypothesis, `equation.monoid {pow-comm p, pow-comm1 (inv p)}` (`pow-comm`, [LemmaHints]). */
  private val lemmaHints: () -> List<ConcreteExpression> = { emptyList() },
) : ProofStepGenerator<ArendGoal> {
  companion object {
    /** Added to [cost] for rewriting with the induction hypothesis rather than applying it. */
    const val REWRITE_EXTRA_COST = 0.2
    /** Added to [cost] for a chain through the induction hypothesis. */
    const val CHAIN_EXTRA_COST = 0.3
    /** Added to [cost] for the solver of the goal's class run with the induction hypothesis as a hint. */
    const val SOLVER_EXTRA_COST = 0.3
    const val MAX_HYPOTHESIS_CHOICES = 4
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val self = goal.definition as? FunctionDefinition ?: return emptyList()
    val smaller = smallerVariables(goal, currentProof)
    if (smaller.isEmpty()) return emptyList()
    val parameters = DependentLink.Helper.toList(self.parameters)
    val context = StepBuilder.context(goal).map { it.second }
    val accept = { typed: Expression -> decreases(typed, self, parameters, smaller, context, strict = true) }
    val acceptNormalizing = { typed: Expression -> decreases(typed, self, parameters, smaller, context, strict = false) }
    val factory = goal.typechecker.factory
    // The eliminated parameters are given their pattern variables, `pow_+ {_} {_} {_} {m}`, `id/=suc {n} q`: left to a
    // meta or to unification, they might be inferred from the first match, which may well be the goal's own instance,
    // or as a term (`pred (suc n)`) that Arend's termination check does not see decreasing
    val names = StepBuilder.context(goal).map { it.first }
    val eliminated = parameters.filter { !it.isExplicit && it.name in smaller }.mapNotNull { parameter ->
      smaller[parameter.name]?.let { vars -> names.find { it.refName == parameter.name && it.refName in vars } }?.let { parameter.name!! to factory.ref(it) }
    }.toMap()
    // As written first (`pmap suc length_++`); with the eliminated parameters explicit only when no call is accepted as
    // written, because its argument is inferred as a term that merely computes to the pattern variable (`id/=suc {n} (pmap pred p)`)
    val steps = AppGenerator(listOf(self), moduleLocation, mapOf(self to cost), accept).generate(goal, currentProof).toMutableList()
    if (steps.isEmpty() && eliminated.isNotEmpty()) steps += AppGenerator(listOf(self), moduleLocation, mapOf(self to cost), acceptNormalizing, fixedImplicits = eliminated).generate(goal, currentProof)
    /**
     * The recursive call: eliminated parameters get their pattern variables; with [fixImplicits], the implicit
     * parameters not eliminated are passed on unchanged (`Big_<=_join1 {_} {x} {l} i`), as structural recursion
     * keeps them and as a chain's open end cannot infer them; explicit ones are goals or holes.
     */
    fun call(openExplicit: Boolean, fixImplicits: Boolean = false): ConcreteExpression {
      val arguments = parameters.map { parameter ->
        val variable = smaller[parameter.name]?.let { vars -> names.find { it.refName == parameter.name && it.refName in vars } }
          ?: if (fixImplicits && !parameter.isExplicit && parameter.name !in smaller) names.find { it.refName == parameter.name } else null
        val expression = if (variable != null) factory.ref(variable) else if (parameter.isExplicit && openExplicit) factory.goal() else factory.hole()
        factory.arg(expression, parameter.isExplicit)
      }
      return factory.app(factory.ref(self.ref), arguments)
    }
    // The induction hypothesis of an equation is rewritten with; the meta infers the call's arguments
    // from the first match, which the decrease check then inspects in the core term
    if (rewriteMetas != null && RewriteGenerator.lemmaSides(self) != null && RewriteGenerator.equationSides(goal.expectedType) != null) {
      for (meta in listOf(rewriteMetas.rewrite, rewriteMetas.rewriteI)) {
        val term = factory.app(factory.ref(meta), true, call(openExplicit = true), factory.goal())
        StepBuilder.build(goal, currentProof, term, cost + REWRITE_EXTRA_COST, moduleLocation, accept)?.let { steps.add(it) }
      }
    }
    // The solver of the goal's class, with the hypothesis instantiated as a hint besides the context's equations:
    // `equation.monoid {p, pow-comm1 {A} {a} {b} p {n}}` (`pow-comm1`); its explicit arguments are variables of the context
    ClosingGenerator.solverFor(goal, solvers)?.let { (solver, _) ->
      val explicit = parameters.filter { it.isExplicit }
      val contextEntries = StepBuilder.context(goal)
      val choices = explicit.map { parameter -> contextEntries.filter { (_, binding) -> PremiseRetriever.head(parameter.type)?.let { h -> PremiseRetriever.head(binding.type) == h } == true }.map { it.first } }
      if (choices.none { it.isEmpty() }) {
        val equations = contextEntries.filter { (_, binding) -> RewriteGenerator.equationSides(binding.type) != null }.map { factory.ref(it.first) }
        for (args in combinations(choices).take(MAX_HYPOTHESIS_CHOICES)) {
          val arguments = ArrayDeque(args)
          val hypothesis = factory.app(factory.ref(self.ref), parameters.map { parameter ->
            val variable = smaller[parameter.name]?.let { vars -> names.find { it.refName == parameter.name && it.refName in vars } }
            factory.arg(if (parameter.isExplicit) factory.ref(arguments.removeFirst()) else if (variable != null) factory.ref(variable) else names.find { it.refName == parameter.name }?.let { factory.ref(it) } ?: factory.hole(), parameter.isExplicit)
          })
          // The solver rewrites with its hints in order and fails when one no longer occurs, so the hypotheses are also
          // left out (`p : a * b = b * a` rewritten first hides `pow (a * b) n` from the induction hypothesis), and lemma
          // instances are added one at a time, then all: `equation.monoid {pow-comm p, pow-comm1 (inv p)}` (`pow-comm`)
          val instances by lazy { lemmaHints() }
          val attempts: Sequence<Pair<List<ConcreteExpression>, Double>> = sequence {
            yield((equations + hypothesis) to 0.0)
            yield(listOf(hypothesis) to 0.0)
            for (group in LemmaHints.groups(instances)) {
              yield((listOf(hypothesis) + group) to ClosingGenerator.LEMMA_HINT_COST)
              yield((equations + hypothesis + group) to ClosingGenerator.LEMMA_HINT_COST)
            }
          }
          val tried = HashSet<String>()
          val started = System.currentTimeMillis()
          for ((hints, extra) in attempts) {
            if (System.currentTimeMillis() - started > ClosingGenerator.SOLVER_BUDGET_MILLIS) break
            val term = ClosingGenerator.hinted(factory, solver, hints)
            if (!tried.add(term.toString())) continue
            val before = System.currentTimeMillis()
            val step = StepBuilder.build(goal, currentProof, term, cost + SOLVER_EXTRA_COST + extra, moduleLocation, acceptNormalizing, limitMillis = StepBuilder.SOLVER_TYPECHECK_MILLIS)
            if (step != null) { steps.add(step); break }
            // A run abandoned at its limit: the solver is slow on this goal, further hint sets are not tried
            if (System.currentTimeMillis() - before >= StepBuilder.SOLVER_TYPECHECK_MILLIS - 100) break
          }
        }
      }
    }
    // A relation being proved, of the kind the hypothesis concludes, is reached by a chain through the hypothesis:
    // its other arguments are inferred from the ends of the chain
    val conclusion = ConclusionMatcher.conclusion(self)
    if (chains.isNotEmpty() && conclusion != null && ConclusionMatcher.relationSides(goal.expectedType) != null &&
      PremiseRetriever.headKey(conclusion) != null && PremiseRetriever.headKey(conclusion) == PremiseRetriever.headKey(goal.expectedType)) {
      for (chain in chains) {
        for (fixImplicits in listOf(true, false)) {
          val hypothesis = call(openExplicit = false, fixImplicits = fixImplicits)
          StepBuilder.build(goal, currentProof, factory.app(factory.ref(chain), true, hypothesis, factory.goal()), cost + CHAIN_EXTRA_COST, moduleLocation, accept)?.let { steps.add(it) }
          StepBuilder.build(goal, currentProof, factory.app(factory.ref(chain), true, factory.goal(), hypothesis), cost + CHAIN_EXTRA_COST, moduleLocation, accept)?.let { steps.add(it) }
        }
      }
    }
    return steps
  }

  /**
   * For each parameter the enclosing `\case \elim`s of [currentProof] split, by name, the names of
   * the variables bound strictly inside the constructor patterns of the clauses containing [goal].
   */
  private fun smallerVariables(goal: ArendGoal, currentProof: Proof<ArendGoal>?): Map<String, Set<String>> {
    val proof = currentProof as? ArendProof ?: return emptyMap()
    val target = proof.getGoals()[goal] ?: return emptyMap()
    val result = HashMap<String, MutableSet<String>>()
    var found = false
    proof.getProof()?.accept(object : BaseConcreteExpressionVisitor<Void?>() {
      override fun visitCase(expr: Concrete.CaseExpression, params: Void?): Concrete.Expression {
        for (clause in expr.clauses) {
          val before = found
          clause.expression?.accept(this, null)
          if (found && !before) {
            // This clause's patterns are in effect for the goal
            expr.arguments.zip(clause.patterns).forEach { (argument, pattern) ->
              val eliminated = (argument.expression as? Concrete.ReferenceExpression)?.takeIf { argument.isElim }?.referent?.refName ?: return@forEach
              if (pattern is Concrete.ConstructorPattern) result.getOrPut(eliminated) { HashSet() } += variables(pattern)
            }
            return expr
          }
        }
        return expr
      }

      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression {
        if (expr === target) found = true
        return expr
      }
    }, null)
    return result
  }

  private fun variables(pattern: Concrete.Pattern): Set<String> = when (pattern) {
    is Concrete.NamePattern -> setOfNotNull(pattern.referable?.refName)
    is Concrete.ConstructorPattern -> pattern.patterns.flatMapTo(HashSet()) { variables(it) }
    is Concrete.TuplePattern -> pattern.patterns.flatMapTo(HashSet()) { variables(it) }
    else -> emptySet()
  }

  /**
   * Whether every call of [self] in [typed] decreases: for the eliminated parameters, some argument
   * strictly smaller than its parameter and the rest the parameters themselves. The other arguments
   * do not matter to termination and may be anything, as `\lam q => p (suc<suc q)` in `-'=0`.
   */
  private fun decreases(typed: Expression, self: FunctionDefinition, parameters: List<DependentLink>, smaller: Map<String, Set<String>>, context: List<Binding>, strict: Boolean = true): Boolean {
    var ok = true
    var calls = 0
    typed.accept(object : VoidExpressionVisitor<Void?>() {
      override fun visitFunCall(expr: FunCallExpression, params: Void?): Void? {
        if (expr.definition == self) {
          calls++
          var strictly = false
          for ((parameter, rawArgument) in parameters.zip(expr.defCallArguments)) {
            // An argument inferred from a hypothesis's type is a solved inference variable standing for the variable
            var argument: Expression = rawArgument
            while (argument is org.arend.core.expr.InferenceReferenceExpression && argument.substExpression != null) argument = argument.substExpression
            // or for a term that computes to it, `pred (suc n)` inferred from `q : pred (suc n) = ...`
            if (!strict && argument !is ReferenceExpression) argument = argument.normalize(org.arend.ext.core.ops.NormalizationMode.WHNF)
            val binding = (argument as? ReferenceExpression)?.binding
            when {
              binding == parameter -> {}
              parameter.name !in smaller -> {}
              // A variable of the branch bound inside the pattern that replaced the parameter
              binding != null && binding != parameter && binding in context && binding.name in smaller[parameter.name].orEmpty() -> strictly = true
              else -> ok = false
            }
          }
          if (!strictly) ok = false
        }
        return super.visitFunCall(expr, params)
      }
    }, null)
    return ok && calls > 0
  }

  private fun <T> combinations(choices: List<List<T>>): Sequence<List<T>> =
    if (choices.isEmpty()) sequenceOf(emptyList()) else sequence {
      for (first in choices[0]) for (rest in combinations(choices.drop(1))) yield(listOf(first) + rest)
    }
}
