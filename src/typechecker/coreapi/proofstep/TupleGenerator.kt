package typechecker.coreapi.proofstep

import org.arend.core.context.param.DependentLink
import org.arend.core.expr.SigmaExpression
import org.arend.ext.module.ModuleLocation
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/** Introduction of a pair: `({?}, {?})` for a goal `\Sigma A B`, one subgoal per component. */
class TupleGenerator(private val moduleLocation: ModuleLocation, private val cost: Double = 0.5) : ProofStepGenerator<ArendGoal> {
  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val sigma = StepBuilder.unfold(goal.expectedType) as? SigmaExpression ?: return emptyList()
    val factory = goal.typechecker.factory
    val fields = DependentLink.Helper.toList(sigma.parameters)
    if (fields.isEmpty()) return emptyList()
    val term = factory.tuple(fields.map { factory.goal() })
    return listOfNotNull(StepBuilder.build(goal, currentProof, term, cost + fields.size * AppGenerator.SUBGOAL_COST, moduleLocation))
  }
}
