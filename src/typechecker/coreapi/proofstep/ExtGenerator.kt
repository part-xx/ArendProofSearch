package typechecker.coreapi.proofstep

import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.SigmaExpression
import org.arend.core.expr.UniverseExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Extensionality: `ext {?}` for an equality whose sides are functions, pairs, records, sets or
 * propositions, which arend-lib's `ext` meta reduces to the equalities of their components, or to
 * `P <-> Q` for propositions (`<->_=`, `SetIm_id`). The meta states the subgoal.
 */
class ExtGenerator(private val moduleLocation: ModuleLocation, private val ext: ArendRef, private val cost: Double = 1.0) : ProofStepGenerator<ArendGoal> {

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val (left, _) = RewriteGenerator.equationSides(goal.expectedType) ?: return emptyList()
    val type = left.type?.normalize(NormalizationMode.WHNF) ?: return emptyList()
    if (type !is PiExpression && type !is SigmaExpression && type !is ClassCallExpression && type !is UniverseExpression) return emptyList()
    val factory = goal.typechecker.factory
    return listOfNotNull(StepBuilder.build(goal, currentProof, factory.app(factory.ref(ext), true, factory.goal()), cost, moduleLocation))
  }
}
