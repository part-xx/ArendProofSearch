package typechecker.impl.proofstep

import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.Definition
import org.arend.ext.error.ErrorReporter
import org.arend.ext.module.LongName
import org.arend.ext.module.ModulePath
import org.arend.naming.reference.TCDefReferable
import org.arend.naming.scope.Scope
import org.arend.naming.scope.ScopeFactory
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import typechecker.Goal
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.impl.ArendGoal

class HeuristicStepGenerator(private val checker: ArendChecker, private val server: ArendServer, private val libName: String, private val modulePath: ModulePath): ProofStepGenerator {
  private val premisesNames: List<String> = listOf("TotalOrder.meet-isMin")

  private fun ensureTypechecked(tcReferable: TCDefReferable, errorReporter: ErrorReporter) {
    if (tcReferable.typechecked != null) return

    // 1. Get the FullName of the referable
    val fullName = tcReferable.refFullName
    val module = fullName.module ?: return

    // 2. Get a checker for the module containing this definition
    val checker = server.getCheckerFor(listOf(module))

    // 3. Trigger typechecking via the public API
    // This will typecheck the definition and all its dependencies
    checker.typecheck(
      listOf(fullName),
      errorReporter,
      UnstoppableCancellationIndicator.INSTANCE,
      ProgressReporter.empty()
    )
  }

  private fun stringToCallableDefinition(goal: ArendGoal, fullName: String): CallableDefinition? {
    checker.resolveModules(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
    val moduleLocation = server.findModule(modulePath, libName, false, true) ?: return null
    val group = server.getRawGroup(moduleLocation) ?: return null
    val moduleScopeProvider = server.getModuleScopeProvider(libName, false)
    val scope = ScopeFactory.forGroup(group, moduleScopeProvider)
    val path = LongName.fromString(fullName).toList()
    val referable = Scope.resolveName(scope, path)
    val tcReferable = referable as? TCDefReferable
      ?: (referable as? org.arend.ext.reference.DataContainer)?.data as? TCDefReferable
      ?: return null

    var definition = goal.typechecker.getCoreDefinition(tcReferable)
    if (definition == null) {
      ensureTypechecked(tcReferable, goal.typechecker.errorReporter)
      definition = goal.typechecker.getCoreDefinition(tcReferable)
    }

    return definition as? CallableDefinition
  }

  override fun generate(goal: Goal): List<ProofStep> {
    val arendGoal = goal as? ArendGoal ?: return emptyList()
    val moduleLocation = server.findModule(modulePath, libName, false, true) ?: return emptyList()
    return AppGenerator(server, premisesNames.mapNotNull { stringToCallableDefinition(arendGoal, it) }, moduleLocation).generate(arendGoal)
  }
}