package typechecker.coreapi.proofstep

import org.arend.core.expr.ClassCallExpression
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * A record or class instance built field by field, `\new Decide { | E => E | decide => {?} }`, as arend-lib's
 * `\cowith` proofs do (`dec_decide : Decide E \cowith | decide => d`, `Inv.lmake`): the fields the goal's class
 * call already implements are copied, the others become goals, in the class's order, so that a later field's
 * type may mention an earlier one. Applies to a goal whose type is a class call with a field left to implement.
 */
class NewGenerator(private val moduleLocation: ModuleLocation, private val cost: Double = 0.8) : ProofStepGenerator<ArendGoal> {
  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val classCall = goal.expectedType.normalize(NormalizationMode.WHNF) as? ClassCallExpression ?: return emptyList()
    val factory = goal.typechecker.factory
    val fields = classCall.definition.allFields.toList()
    val open = fields.filter { !classCall.isImplemented(it) }
    if (open.isEmpty()) return emptyList()
    val implementations = ArrayList<org.arend.ext.concrete.ConcreteClassElement>()
    for (field in fields) {
      val implemented = classCall.getAbsImplementationHere(field)
      val expression: ConcreteExpression = when {
        implemented != null -> CoreToConcrete.convert(implemented, goal) ?: return emptyList()
        classCall.isImplemented(field) -> continue
        else -> factory.goal()
      }
      implementations.add(factory.implementation(field.ref, expression))
    }
    val term = factory.newExpr(factory.classExt(factory.ref(classCall.definition.ref), implementations))
    return listOfNotNull(StepBuilder.build(goal, currentProof, term, cost + (open.size - 1) * AppGenerator.SUBGOAL_COST, moduleLocation))
  }
}
