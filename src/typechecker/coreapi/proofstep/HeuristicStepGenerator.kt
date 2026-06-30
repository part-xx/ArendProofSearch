package typechecker.coreapi.proofstep

import org.arend.ext.module.ModulePath
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import typechecker.Proof
import typechecker.ProofStep
import typechecker.coreapi.ArendGoal

class HeuristicStepGenerator(
  checker: ArendChecker,
  server: ArendServer,
  libName: String,
  modulePath: ModulePath,
  private val premisesNames: List<String> = listOf("TotalOrder.meet-isMin")
): BaseStepGenerator(checker, server, libName, modulePath) {

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val scope = getScope() ?: return emptyList()
    val moduleLocation = getModuleLocation() ?: return emptyList()

    val premises = premisesNames.mapNotNull { fullName ->
      val tcReferable = resolveName(scope, fullName) ?: return@mapNotNull null
      getCallableDefinition(goal, tcReferable)
    }

    if (premises.isEmpty()) return emptyList()
    return AppGenerator(server, premises, moduleLocation).generate(goal, currentProof)
  }
}
