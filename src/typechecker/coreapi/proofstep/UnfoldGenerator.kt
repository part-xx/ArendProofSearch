package typechecker.coreapi.proofstep

import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.CaseExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FunCallExpression
import org.arend.core.expr.visitor.VoidExpressionVisitor
import org.arend.ext.core.definition.CoreFunctionDefinition
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * `unfold f {?}` for a function `f` of the goal defined by an expression, when unfolding exposes
 * something to work with that the goal does not show: a `\case` to split with `mcases`
 * (`unfold dec<_<= (mcases …)`), or a function with equations to rewrite (`unfold (-) (rewrite
 * negative-isInv …)`: `x - y` is `x + negative y`). Rewriting matches the goal as written, so
 * what `f` hides is out of its reach until unfolded.
 */
class UnfoldGenerator(
  private val moduleLocation: ModuleLocation,
  private val unfold: ArendRef,
  private val cost: Double = 1.0,
  private val maxFunctions: Int = 3,
  /** The equations the goal may be rewritten with: unfolding is also worth it when it exposes a side of one (`negative (negative x)` in `x - negative y`). */
  private val rewriteLemmas: List<CallableDefinition> = emptyList(),
) : ProofStepGenerator<ArendGoal> {
  companion object {
    /** At most this many rewrite lemmas are checked against the unfolded goal. */
    const val MAX_LEMMAS_CHECKED = 20
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val functions = LinkedHashSet<FunctionDefinition>()
    val goalSymbols = EquationRetriever.functionSymbols(goal.expectedType).toSet()
    goal.expectedType.accept(object : VoidExpressionVisitor<Void?>() {
      override fun visitFunCall(expr: FunCallExpression, params: Void?): Void? {
        val definition = expr.definition
        val body = definition.actualBody as? Expression
        val kind = definition.kind
        if (body != null && (kind == CoreFunctionDefinition.Kind.FUNC || kind == CoreFunctionDefinition.Kind.SFUNC || kind == CoreFunctionDefinition.Kind.TYPE) &&
          (exposes(body, goalSymbols) || exposesRewrite(goal.expectedType, definition))) functions.add(definition)
        return super.visitFunCall(expr, params)
      }
    }, null)
    val factory = goal.typechecker.factory
    return functions.take(maxFunctions).mapNotNull { function ->
      val term = factory.app(factory.ref(unfold), true, factory.ref(function.ref), factory.goal())
      StepBuilder.build(goal, currentProof, term, cost, moduleLocation)
    }
  }

  /** Whether unfolding [function] in [goal] exposes a side of one of the rewrite lemmas that the goal as written does not show. */
  private fun exposesRewrite(goal: Expression, function: FunctionDefinition): Boolean {
    if (rewriteLemmas.isEmpty()) return false
    val unfolded = goal.unfold(setOf(function), null, false, false) as? Expression ?: return false
    return rewriteLemmas.take(MAX_LEMMAS_CHECKED).any { lemma ->
      val before = ConclusionMatcher.rewriteSideScores(lemma, goal) ?: return@any false
      val after = ConclusionMatcher.rewriteSideScores(lemma, unfolded) ?: return@any false
      (before.first == null && after.first != null) || (before.second == null && after.second != null)
    }
  }

  /** Whether [body] has a `\case`, or applies a function the goal does not, [goalSymbols]. */
  private fun exposes(body: Expression, goalSymbols: Set<Symbol>): Boolean {
    var hasCase = false
    body.accept(object : VoidExpressionVisitor<Void?>() {
      override fun visitCase(expr: CaseExpression, params: Void?): Void? { hasCase = true; return null }
    }, null)
    return hasCase || EquationRetriever.functionSymbols(body).any { it !in goalSymbols }
  }
}
