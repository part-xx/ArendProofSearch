package typechecker.coreapi.proofstep

import org.arend.core.expr.DataCallExpression
import org.arend.core.expr.PiExpression
import org.arend.ext.core.ops.NormalizationMode
import typechecker.coreapi.ArendGoal

/**
 * The constructors of the goal's data type, the introduction rules: `byLeft` and `byRight` for
 * `A || B`, `inP` for `∃`, `suc<suc` for `suc n < suc m`. They need no search, and lemmas that
 * merely conclude the same type would crowd them out of a proof search's capped results.
 */
class ConstructorRetriever(private val cost: Double = 0.5) : PremiseRetriever {
  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> {
    var type = goal.expectedType.normalize(NormalizationMode.WHNF)
    while (type is PiExpression) type = type.codomain.normalize(NormalizationMode.WHNF)
    val dataCall = type as? DataCallExpression ?: return emptyList()
    // Only the constructors whose patterns match the type's indices, e.g. just suc<suc for `suc n < suc m`
    val constructors = dataCall.matchedConstructors?.map { it.definition } ?: dataCall.definition.constructors
    return constructors.mapNotNull { constructor ->
      val module = constructor.ref.location?.modulePath ?: return@mapNotNull null
      PremiseCandidate(constructor.ref.refLongName.toString(), module.toString(), cost)
    }
  }
}
