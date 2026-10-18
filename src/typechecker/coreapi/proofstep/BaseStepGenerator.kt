package typechecker.coreapi.proofstep

import org.arend.core.definition.CallableDefinition
import org.arend.error.DummyErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.LongName
import org.arend.ext.module.ModuleLocation
import org.arend.ext.module.ModulePath
import org.arend.naming.reference.Referable
import org.arend.naming.reference.TCDefReferable
import org.arend.naming.scope.MergeScope
import org.arend.naming.scope.Scope
import org.arend.naming.scope.ScopeFactory
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

abstract class BaseStepGenerator(protected val checker: ArendChecker, protected val server: ArendServer, protected val libName: String, protected val modulePath: ModulePath): ProofStepGenerator<ArendGoal> {
  protected fun getCallableDefinition(goal: ArendGoal, tcReferable: TCDefReferable): CallableDefinition? {
    val definition = goal.typechecker.getCoreDefinition(tcReferable)
    return definition as? CallableDefinition
  }

  /** Resolves [fullName] to a definition; with [typecheck], one that nothing has needed yet is typechecked first. */
  protected fun resolveName(scope: Scope, fullName: String, typecheck: Boolean = true): TCDefReferable? {
    val referable = resolveReferable(scope, fullName)
    val tcReferable = (referable as? TCDefReferable)
      ?: (referable as? org.arend.ext.reference.DataContainer)?.data as? TCDefReferable
      ?: return null
    if (typecheck) ensureTypechecked(tcReferable)
    return tcReferable
  }

  /** Typechecks the definition of [referable] if nothing has needed it yet, e.g. a lemma of a dependency. */
  private fun ensureTypechecked(referable: TCDefReferable) {
    if (referable.typechecked != null) return
    val module = referable.location ?: return
    server.getCheckerFor(listOf(module)).typecheck(
      listOf(FullName(module, referable.refLongName)), DummyErrorReporter.INSTANCE,
      UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty()
    )
  }

  /** Resolves [fullName] to any referable, including metas, which are not [TCDefReferable]s. */
  protected fun resolveReferable(scope: Scope, fullName: String): Referable? =
    Scope.resolveName(scope, LongName.fromString(fullName).toList())

  protected fun getScope(): Scope? = getScope(modulePath)

  /** The scope of [modulePath], a module of this library, of one of its dependencies, or Prelude. */
  protected fun getScope(modulePath: ModulePath): Scope? {
    val moduleLocation = server.findModule(modulePath, libName, false, true) ?: return null
    val group = server.getRawGroup(moduleLocation) ?: return null
    val moduleScopeProvider = server.getModuleScopeProvider(libName, false)
    val groupScope = ScopeFactory.forGroup(group, moduleScopeProvider)
    val moduleScope = moduleScopeProvider.moduleScope
    val mergedScope = if (moduleScope != null) MergeScope(true, groupScope, moduleScope) else groupScope
    return mergedScope
  }

  /** Looked up once: `findModule` asks the server to update the module, which re-reads and re-parses its source. */
  private val cachedModuleLocation: ModuleLocation? by lazy { server.findModule(modulePath, libName, false, true) }

  protected fun getModuleLocation(): ModuleLocation? = cachedModuleLocation

  protected fun stringToCallableDefinition(goal: ArendGoal, fullName: String): CallableDefinition? {
    val scope = getScope() ?: return null
    val tcReferable = resolveName(scope, fullName) ?: return null

    return getCallableDefinition(goal, tcReferable)
  }
}
