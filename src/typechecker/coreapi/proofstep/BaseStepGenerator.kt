package typechecker.coreapi.proofstep

import org.arend.core.definition.CallableDefinition
import org.arend.ext.module.LongName
import org.arend.ext.module.ModuleLocation
import org.arend.ext.module.ModulePath
import org.arend.naming.reference.TCDefReferable
import org.arend.naming.scope.MergeScope
import org.arend.naming.scope.Scope
import org.arend.naming.scope.ScopeFactory
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

abstract class BaseStepGenerator(protected val checker: ArendChecker, protected val server: ArendServer, protected val libName: String, protected val modulePath: ModulePath): ProofStepGenerator<ArendGoal> {
  protected fun getCallableDefinition(goal: ArendGoal, tcReferable: TCDefReferable): CallableDefinition? {
    val definition = goal.typechecker.getCoreDefinition(tcReferable)
    return definition as? CallableDefinition
  }

  protected fun resolveName(scope: Scope, fullName: String): TCDefReferable? {
    val path = LongName.fromString(fullName).toList()
    val referable = Scope.resolveName(scope, path)
    return (referable as? TCDefReferable)
      ?: (referable as? org.arend.ext.reference.DataContainer)?.data as? TCDefReferable
  }

  protected fun getScope(): Scope? {
    val moduleLocation = server.findModule(modulePath, libName, false, true) ?: return null
    val group = server.getRawGroup(moduleLocation) ?: return null
    val moduleScopeProvider = server.getModuleScopeProvider(libName, false)
    val groupScope = ScopeFactory.forGroup(group, moduleScopeProvider)
    val moduleScope = moduleScopeProvider.moduleScope
    val mergedScope = if (moduleScope != null) MergeScope(true, groupScope, moduleScope) else groupScope
    return mergedScope
  }

  protected fun getModuleLocation(): ModuleLocation? {
    return server.findModule(modulePath, libName, false, true)
  }

  protected fun stringToCallableDefinition(goal: ArendGoal, fullName: String): CallableDefinition? {
    val scope = getScope() ?: return null
    val tcReferable = resolveName(scope, fullName) ?: return null

    return getCallableDefinition(goal, tcReferable)
  }
}
