package typechecker.coreapi.proofstep

import org.arend.core.context.param.DependentLink
import org.arend.core.expr.AppExpression
import org.arend.core.expr.ConCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FieldCallExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.core.ops.CMP
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.typechecking.implicitargs.equations.DummyEquations
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Congruence: for a goal `f a = f a'` whose sides apply the same function to arguments that differ
 * only in the last one, `pmap f {?}` with the subgoal `a = a'` (`pmap suc length_++`, `pmap pos q`).
 * The function is taken from the goal, since the typechecker cannot infer it.
 */
class CongruenceGenerator(private val moduleLocation: ModuleLocation, private val pmap: ArendRef, private val cost: Double = 1.0) : ProofStepGenerator<ArendGoal> {
  companion object {
    /** Added for the lambda form of the function. */
    const val LAMBDA_EXTRA_COST = 0.1
  }


  /** The head of an application and its arguments, outermost application last. */
  private fun application(expr: Expression): Pair<Expression, List<Expression>>? = when (expr) {
    is AppExpression -> {
      val args = ArrayDeque<Expression>()
      var current: Expression = expr
      while (current is AppExpression) {
        args.addFirst(current.argument)
        current = current.function
      }
      current to args.toList()
    }
    is ConCallExpression -> if (expr.defCallArguments.isEmpty()) null else expr to expr.defCallArguments
    is FieldCallExpression -> null
    is DefCallExpression -> if (expr.defCallArguments.isEmpty()) null else expr to expr.defCallArguments
    else -> null
  }

  private fun same(a: Expression, b: Expression) = CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, a, b, null, null)

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val (left, right) = RewriteGenerator.equationSides(goal.expectedType) ?: return emptyList()
    // The shared head may only show after computing, as `suc` in `length (a :: l) = suc (length l) + ...`
    val leftNormalized = left.normalize(NormalizationMode.WHNF)
    val (leftHead, leftArgs) = application(leftNormalized) ?: return emptyList()
    val (rightHead, rightArgs) = application(right.normalize(NormalizationMode.WHNF)) ?: return emptyList()
    if (leftArgs.size != rightArgs.size || leftArgs.isEmpty()) return emptyList()
    if (!leftArgs.dropLast(1).zip(rightArgs.dropLast(1)).all { (a, b) -> same(a, b) } || same(leftArgs.last(), rightArgs.last())) return emptyList()
    val factory = goal.typechecker.factory
    val function: ConcreteExpression = if (leftHead is DefCallExpression && leftHead !is FieldCallExpression) {
      if (rightHead !is DefCallExpression || leftHead.definition != rightHead.definition) return emptyList()
      // The definition itself is the function when its earlier parameters are implicit, as `length {A}` for `length l`
      val params = DependentLink.Helper.toList(leftHead.definition.parameters)
      if (params.size != leftArgs.size || params.dropLast(1).any { it.isExplicit }) return emptyList()
      factory.ref(leftHead.definition.ref)
    } else {
      // A variable applied to arguments, as `f a b`, or a class operation, as `a + x` (arend-lib's `pmap (a +)` in
      // `fit_BigSum`, `BigSum-unique2`): the function is the head applied to the leading arguments
      if (!same(leftHead, rightHead)) return emptyList()
      CoreToConcrete.convert(leftArgs.dropLast(1).fold(leftHead) { f, a -> AppExpression.make(f, a, true) }, goal) ?: return emptyList()
    }
    val term = factory.app(factory.ref(pmap), true, function, factory.goal())
    // Or the function as a lambda, `pmap (\lam z => suc z)`: needed when the head alone does not determine its implicit
    // arguments, as `suc` of `Fin` (arend-lib's `fin_nat-inj`)
    val z = factory.local("z")
    val contextMap = StepBuilder.context(goal).associate { it.second to it.first }
    // The parameter is typed, `\lam (z : Fin n) => suc z`: with a hole as the path, nothing else says what `z` is
    val parameter = leftArgs.last().type?.let { CoreToConcrete.convert(it, contextMap, factory) }?.let { factory.param(true, listOf(z), it) } ?: factory.param(true, z)
    val lambda = CoreToConcrete.convert(leftNormalized, contextMap, factory, java.util.IdentityHashMap<Expression, ConcreteExpression>().apply { put(leftArgs.last(), factory.ref(z)) })
      ?.let { body -> factory.app(factory.ref(pmap), true, factory.lam(listOf(parameter), body), factory.goal()) }
    return listOfNotNull(StepBuilder.build(goal, currentProof, term, cost, moduleLocation), lambda?.let { StepBuilder.build(goal, currentProof, it, cost + LAMBDA_EXTRA_COST, moduleLocation) })
  }
}
