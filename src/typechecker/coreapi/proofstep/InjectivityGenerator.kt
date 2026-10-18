package typechecker.coreapi.proofstep

import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.Expression
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Injectivity by a destructor: for a goal `a = b` and a hypothesis `p : f a = f b` whose sides apply
 * the same head, `pmap g p` with a function `g` that undoes `f` by computation, as arend-lib's
 * `pmap pred p` (`id/=suc`, `fin_nat-inj`), `pmap iabs p` (`unpos`) and `pmap (fpred x) p` (`unfsuc`).
 * The functions come from [DestructorRetriever]; the other explicit parameters of `g` (`fpred`'s default)
 * are filled with variables of the context. Only hypotheses with one head on both sides activate it.
 */
class InjectivityGenerator(
  private val moduleLocation: ModuleLocation,
  private val pmap: ArendRef,
  private val destructors: Map<CallableDefinition, Double>,
) : ProofStepGenerator<ArendGoal> {
  private val debug = System.getProperty("proofsearch.debug") == "true"

  companion object {
    const val MAX_ARGUMENT_CHOICES = 4
    const val FORWARD_EXTRA_COST = 0.2
  }

  /**
   * Whether the hypothesis [name] bound by the step has sides the destructor peeled: each computes to a
   * subterm of the original side (`pred (suc n)` to `n`), not to something else (`fac (suc n)` to `suc n * fac n`).
   */
  private fun computes(step: ProofStep<ArendGoal>, name: String, original: Pair<Expression, Expression>): Boolean {
    val inner = step.proof.goals().firstOrNull() ?: return false
    val binding = StepBuilder.context(inner).firstOrNull { it.first.refName == name }?.second ?: return false
    val (a, b) = RewriteGenerator.equationSides(binding.type) ?: return false
    fun peeled(side: Expression, from: Expression): Boolean {
      val reduced = side.normalize(org.arend.ext.core.ops.NormalizationMode.WHNF)
      // The new hypothesis lives in the step's own context, whose bindings are other objects than the goal's: compared as printed too
      val result = ConclusionMatcher.subterms(from).drop(1).any {
        org.arend.core.expr.visitor.CompareVisitor.compare(org.arend.typechecking.implicitargs.equations.DummyEquations.getInstance(), org.arend.ext.core.ops.CMP.EQ, reduced, it, null, null) || reduced.toString() == it.toString()
      }
      if (!result && debug) println("Injectivity: $side (${side.javaClass.simpleName}) reduces to $reduced (${reduced.javaClass.simpleName}), not a proper subterm of $from (${from.javaClass.simpleName}: ${ConclusionMatcher.subterms(from).drop(1)})")
      return result
    }
    return peeled(a, original.first) && peeled(b, original.second)
  }

  /** Whether the goal is already under a forward step mapping the hypothesis [name]: mapping it again adds nothing. */
  private fun alreadyMapped(goal: ArendGoal, currentProof: Proof<ArendGoal>?, name: String): Boolean {
    val proof = currentProof as? typechecker.coreapi.ArendProof ?: return false
    val target = proof.getGoals()[goal] ?: return false
    var found = false
    var result = false
    proof.getProof()?.accept(object : org.arend.term.concrete.BaseConcreteExpressionVisitor<Void?>() {
      override fun visitCase(expr: org.arend.term.concrete.Concrete.CaseExpression, params: Void?): org.arend.term.concrete.Concrete.Expression {
        val before = found
        expr.clauses.forEach { it.expression?.accept(this, null) }
        if (found && !before && expr.arguments.any { arg -> !arg.isElim && (arg.expression as? org.arend.term.concrete.Concrete.AppExpression)?.arguments?.lastOrNull()?.expression.let { (it as? org.arend.term.concrete.Concrete.ReferenceExpression)?.referent?.refName == name } }) result = true
        return expr
      }
      override fun visitGoal(expr: org.arend.term.concrete.Concrete.GoalExpression, params: Void?): org.arend.term.concrete.Concrete.Expression { if (expr === target) found = true; return expr }
    }, null)
    return result
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    if (destructors.isEmpty() || goal.expectedType is org.arend.core.expr.PiExpression) return emptyList()
    // Mapping closes an equation goal outright; for any goal the mapped hypothesis may be kept for later
    val equationGoal = RewriteGenerator.equationSides(goal.expectedType) != null
    val factory = goal.typechecker.factory
    val context = StepBuilder.context(goal)
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    for ((p, binding) in context) {
      val (a, b) = RewriteGenerator.equationSides(binding.type) ?: continue
      val head = PremiseRetriever.headKey(a) ?: continue
      if (head != PremiseRetriever.headKey(b)) continue
      val mapped = alreadyMapped(goal, currentProof, p.refName)
      for ((destructor, cost) in destructors) {
        val parameters = (destructor as? FunctionDefinition)?.let { DependentLink.Helper.toList(it.parameters).filter { p -> p.isExplicit } } ?: continue
        if (parameters.isEmpty()) continue
        val choices = parameters.dropLast(1).map { parameter -> context.filter { (_, b) -> sameKind(parameter.type, b.type) }.map { it.first } }
        if (choices.any { it.isEmpty() }) continue
        for (args in combinations(choices).take(MAX_ARGUMENT_CHOICES)) {
          val function = if (args.isEmpty()) factory.ref(destructor.ref) else factory.app(factory.ref(destructor.ref), true, args.map { factory.ref(it) })
          val term = factory.app(factory.ref(pmap), true, function, factory.ref(p))
          if (equationGoal) StepBuilder.build(goal, currentProof, term, cost * AppGenerator.CLOSING_FACTOR, moduleLocation)?.let { steps.add(it) }
          // Or the mapped hypothesis is kept for later as a pattern variable, `\case pmap pred p \with { | q => {?} }`,
          // for the argument of a recursive call (`id/=suc (pmap pred p)`); only when the destructor computes on the sides
          val q = factory.local(generateSequence("q") { "$it'" }.first { name -> context.none { it.first.refName == name } })
          val forward = factory.caseExpr(false, listOf(factory.caseArg(term, null, null)), null, null, listOf(factory.clause(listOf(factory.refPattern(q, null)), factory.goal())))
          if (!mapped) {
            val built = StepBuilder.build(goal, currentProof, forward, cost + FORWARD_EXTRA_COST, moduleLocation)
            if (built != null && computes(built, q.refName, a to b)) steps.add(built)
            else if (debug) println("Injectivity: forward step with ${destructor.ref.refName} on ${p.refName} ${if (built == null) "rejected" else "does not peel"}")
          }
        }
      }
    }
    return steps
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
