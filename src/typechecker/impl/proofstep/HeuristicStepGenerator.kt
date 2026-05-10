package typechecker.impl.proofstep

import org.arend.ext.module.ModulePath
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import typechecker.Goal
import typechecker.ProofStep
import typechecker.impl.ArendGoal

class HeuristicStepGenerator(
  checker: ArendChecker,
  server: ArendServer,
  libName: String,
  modulePath: ModulePath,
  private val premisesNames: List<String> = listOf("TotalOrder.meet-isMin")
): BaseStepGenerator(checker, server, libName, modulePath) {

  override fun generate(goal: Goal): List<ProofStep> {
    val arendGoal = goal as? ArendGoal ?: return emptyList()
    val scope = getScope() ?: return emptyList()
    val moduleLocation = getModuleLocation() ?: return emptyList()

    val premises = premisesNames.mapNotNull { fullName ->
      val tcReferable = resolveName(scope, fullName) ?: return@mapNotNull null
      getCallableDefinition(arendGoal, tcReferable)
    }

    if (premises.isEmpty()) return emptyList()
    return AppGenerator(server, premises, moduleLocation).generate(arendGoal)
  }
}