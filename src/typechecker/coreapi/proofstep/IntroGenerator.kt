package typechecker.coreapi.proofstep

import org.arend.core.expr.PiExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/** Introduction: `\lam x => {?}` for a goal of a function type, such as `Not P` or `fsuc x /= 0`. */
class IntroGenerator(private val moduleLocation: ModuleLocation, private val cost: Double = 0.5) : ProofStepGenerator<ArendGoal> {
  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val pi = StepBuilder.unfold(goal.expectedType) as? PiExpression ?: return emptyList()
    val factory = goal.typechecker.factory
    val parameter = pi.parameters
    val used = StepBuilder.context(goal).map { it.first.refName }.toSet()
    var name = parameter.name ?: if (parameter.type.sortOfType?.isProp == true) "p" else "x"
    while (name in used) name += "'"
    val term = factory.lam(listOf(factory.param(parameter.isExplicit, factory.local(name))), factory.goal())
    return listOfNotNull(StepBuilder.build(goal, currentProof, term, cost, moduleLocation))
  }
}
