package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.expr.DataCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.Referable
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Applying a hypothesis of a function type, as arend-lib proofs do with `q r`, `n/=0 idp`, and
 * `absurd (n idp)` for a negated hypothesis `n : Not P` against any goal. Arguments that the
 * function's result mentions are inferred; the others become subgoals. A hypothesis is applied
 * only when what it concludes is about the same thing as the goal, by head.
 */
class HypothesisGenerator(
  private val moduleLocation: ModuleLocation,
  /** `absurd : Empty -> A` of arend-lib's Logic; without it negated hypotheses are only applied to the goal `Empty`. */
  private val absurd: ArendRef? = null,
  private val cost: Double = 0.9,
  private val absurdCost: Double = 1.2,
) : ProofStepGenerator<ArendGoal> {
  companion object {
    /** Added when the hypothesis is applied to a constructor of a variable, `f (suc i)`, rather than to a hole. */
    const val CONSTRUCTOR_ARGUMENT_COST = 0.3
  }


  /** The explicit parameters of a function type and its final codomain. */
  private class Signature(val params: List<DependentLink>, val codomain: Expression)

  private fun signature(type: Expression): Signature? {
    val params = mutableListOf<DependentLink>()
    var current = StepBuilder.unfold(type)
    while (current is PiExpression) {
      params += DependentLink.Helper.toList(current.parameters)
      current = StepBuilder.unfold(current.codomain)
    }
    return if (params.isEmpty()) null else Signature(params, current)
  }

  private fun isEmpty(type: Expression) = (type as? DataCallExpression)?.definition?.let { it.ref.refName == "Empty" && it.constructors.isEmpty() } == true

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    val goalArity = AppGenerator.arity(goal.expectedType)
    val goalIsEmpty = isEmpty(StepBuilder.unfold(goal.expectedType))
    val goalHead = PremiseRetriever.headKey(goal.expectedType)
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    val context = StepBuilder.context(goal)
    for ((ref, binding) in context) {
      val signature = signature(binding.type) ?: continue
      val explicit = signature.params.filter { it.isExplicit }
      // Applied to the goal: the arguments the goal does not supply
      val numArgsToAdd = explicit.size + AppGenerator.arity(signature.codomain) - goalArity
      val concludesGoal = goalHead != null && PremiseRetriever.headKey(signature.codomain) == goalHead
      if (numArgsToAdd in 0..explicit.size && concludesGoal) {
        val (term, opened) = apply(factory, ref, signature, numArgsToAdd)
        StepBuilder.build(goal, currentProof, term, if (opened == 0) cost * AppGenerator.CLOSING_FACTOR else cost + opened * AppGenerator.SUBGOAL_COST, moduleLocation)?.let { steps.add(it) }
        // The first argument as a constructor of a variable of the context, `f (suc i)` for
        // `f : \Pi (i : Fin (suc n)) -> y <= (a :: l) i` and the goal `y <= l i`: a hole there cannot be
        // inferred, since `(a :: l) ?j` and `l i` do not unify, while `(a :: l) (suc i)` computes to `l i`
        if (numArgsToAdd >= 1) {
          for (argument in constructorArguments(factory, explicit[0].type, context)) {
            val (variant, openedVariant) = apply(factory, ref, signature, numArgsToAdd, first = argument)
            // Like the plain application, a variant that closes the goal is cheap: `f (suc i)` ends a branch
            val variantCost = if (openedVariant == 0) (cost + CONSTRUCTOR_ARGUMENT_COST) * AppGenerator.CLOSING_FACTOR else cost + CONSTRUCTOR_ARGUMENT_COST + openedVariant * AppGenerator.SUBGOAL_COST
            StepBuilder.build(goal, currentProof, variant, variantCost, moduleLocation)?.let { steps.add(it) }
          }
        }
      }
      // A refutation: `absurd (h ...)` for `h` concluding Empty
      if (absurd != null && !goalIsEmpty && isEmpty(signature.codomain)) {
        val (application, opened) = apply(factory, ref, signature, explicit.size)
        val term = factory.app(factory.ref(absurd), true, application)
        StepBuilder.build(goal, currentProof, term, absurdCost + opened * AppGenerator.SUBGOAL_COST, moduleLocation)?.let { steps.add(it) }
      }
    }
    return steps
  }

  /** [ref] applied to its first [numArgs] explicit arguments, the first being [first] when given, and the number of them that are subgoals. */
  private fun apply(factory: org.arend.ext.concrete.ConcreteFactory, ref: Referable, signature: Signature, numArgs: Int, first: org.arend.ext.concrete.expr.ConcreteExpression? = null): Pair<org.arend.ext.concrete.expr.ConcreteExpression, Int> {
    val params = signature.params
    val subgoals = params.withIndex().filter { it.value.isExplicit }.take(numArgs).map { (i, param) ->
      params.drop(i + 1).none { StepBuilder.occurs(param, it.type) } && !StepBuilder.occurs(param, signature.codomain)
    }
    val args = subgoals.mapIndexed { i, isSubgoal -> factory.arg(if (i == 0 && first != null) first else if (isSubgoal) factory.goal() else factory.hole(), true) }
    return factory.app(factory.ref(ref), args) to subgoals.drop(if (first != null) 1 else 0).count { it }
  }

  /**
   * `c v` for each constructor `c` of the data type [parameterType] with one explicit argument and each
   * variable `v` of [context] of that argument's type, and each nullary constructor `c`: the values of the
   * parameter built from what is at hand (`f 0` and `f (suc i)` in `Big_meet-univ`, `BigSum_zro`, `fit_BigSum`).
   */
  private fun constructorArguments(factory: org.arend.ext.concrete.ConcreteFactory, parameterType: Expression, context: List<Pair<Referable, Binding>>): List<org.arend.ext.concrete.expr.ConcreteExpression> {
    val dataCall = StepBuilder.unfold(parameterType) as? DataCallExpression ?: return emptyList()
    // The index may be stuck on a variable or an unevaluated call, `Fin (len {a :: l})`: then every constructor
    // is a candidate, and the typechecker decides
    val constructors = dataCall.matchedConstructors?.takeIf { it.isNotEmpty() }?.map { it.definition } ?: dataCall.definition.constructors
    val result = mutableListOf<org.arend.ext.concrete.expr.ConcreteExpression>()
    for (constructor in constructors) {
      val explicit = DependentLink.Helper.toList(constructor.parameters).filter { it.isExplicit }
      // A nullary constructor is a value by itself: `f 0` for `0 : Fin (suc n)`
      if (explicit.isEmpty()) { result.add(factory.ref(constructor.ref)); continue }
      val parameter = explicit.singleOrNull() ?: continue
      for ((ref, binding) in context) {
        // The constructor's parameter type mentions the data type's own parameters; comparing by head is enough,
        // the typechecker decides the rest
        val head = PremiseRetriever.head(parameter.type) ?: continue
        if (PremiseRetriever.head(binding.type) != head) continue
        result.add(factory.app(factory.ref(constructor.ref), true, factory.ref(ref)))
      }
    }
    return result
  }
}
