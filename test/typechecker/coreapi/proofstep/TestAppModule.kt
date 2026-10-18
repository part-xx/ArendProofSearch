package typechecker.coreapi.proofstep

import integration.TestLibrary
import org.arend.core.definition.CallableDefinition
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.Expression
import org.arend.ext.error.GeneralError
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.LongName
import org.arend.naming.reference.Referable
import org.arend.naming.scope.Scope
import org.arend.naming.scope.ScopeFactory
import org.arend.server.ProgressReporter
import org.arend.term.concrete.Concrete
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.CheckTypeVisitor
import search.best_first.BestFirstSearch
import typechecker.Proof
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import kotlin.test.fail

/** Goals of `test-lib/src/TestApp.ard`. */
object TestAppModule : TestModule("TestApp", TestLibrary::load)

/** Goals of the module [name] of the library loaded by [load], and best-first search on them. */
open class TestModule(private val name: String, private val load: () -> TestLibrary?) {
  val module: TestLibrary.Module by lazy {
    load()?.module(name) ?: fail("Could not load module $name")
  }

  class SearchResult(val goal: ArendGoal, val proof: ArendProof?)

  /** Resolves [name] in the scope of the module, e.g. a meta it imports. */
  fun scopeRef(name: String): Referable {
    val scope = ScopeFactory.forGroup(module.group, module.server.getModuleScopeProvider(module.libraryName, false))
    return Scope.resolveName(scope, LongName.fromString(name).toList()) ?: fail("$name is not in scope of ${this.name}")
  }

  fun premises(vararg names: String): List<CallableDefinition> {
    val byName = mutableMapOf<String, CallableDefinition>()
    module.group.traverseGroup { group ->
      val def = group.definition ?: return@traverseGroup
      (def.data.typechecked as? CallableDefinition)?.let { byName[def.data.refName] = it }
    }
    return names.map { byName[it] ?: fail("Premise $it not found in $name") }
  }

  /**
   * Typechecks [defName] and runs [action] on the goal of its `{?}` body. The goal is built once
   * the definition is typechecked: while its body is being checked, the instance arguments of
   * its statement (`<` of an order, `∧` of a lattice) are still inference variables, and a
   * typechecker treats a comparison with an unsolved variable as success.
   */
  fun <T> withGoal(defName: String, action: (ArendGoal) -> T): T {
    val definition = module.group.statements.mapNotNull { it.group?.definition }
      .find { it.data.refName == defName } as? Concrete.FunctionDefinition ?: fail("Definition $defName not found")

    var captured: Pair<CheckTypeVisitor, Concrete.GoalExpression>? = null
    val errors = ListErrorReporter()
    module.server.getCheckerFor(listOf(module.location)).typecheck(
      FullName(module.location, definition.data.refLongName),
      { errorReporter, pool, arendExtension, listener ->
        object : CheckTypeVisitor(errorReporter, pool, arendExtension, listener) {
          override fun visitGoal(expr: Concrete.GoalExpression, expectedType: Expression): TypecheckingResult {
            if (captured == null) captured = this to expr
            return super.visitGoal(expr, expectedType)
          }
        }
      },
      null, errors, UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty()
    )
    // A statement that does not typecheck (an unresolved name, an instance that cannot be inferred) would make any search meaningless
    errors.errorList.filter { it.level == GeneralError.Level.ERROR }.takeIf { it.isNotEmpty() }?.let { fail("$defName does not typecheck: $it") }
    val (typechecker, goalExpression) = captured ?: fail("No goal found in $defName")
    val typechecked = definition.data.typechecked as? FunctionDefinition ?: fail("$defName did not typecheck")
    // The finished definition's result type refers to its final parameters: the context has to be those
    val parameters = DependentLink.Helper.toList(typechecked.parameters)
    val referables = definition.parameters.flatMap { it.referableList }
    if (parameters.size != referables.size) fail("$defName: ${referables.size} parameter names for ${parameters.size} parameters")
    typechecker.context.clear()
    referables.zip(parameters).forEach { (referable, parameter) -> typechecker.context[referable] = parameter }
    return action(ArendGoal(typechecked.resultType, typechecker, goalExpression, typechecked))
  }

  /** Runs best-first search with the generator built by [generator] on the goal of [defName]. */
  fun search(defName: String, generator: (ArendGoal) -> ProofStepGenerator<ArendGoal>, maxExpansions: Int = 200, focusFirstGoal: Boolean = false, openGoalCost: Double = 0.0, maxDepth: Int = BestFirstSearch.MAX_DEPTH): SearchResult =
    withGoal(defName) { goal ->
      val initialProof = object : Proof<ArendGoal> {
        override fun goals() = listOf(goal)
        override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = proof
      }
      println("SEARCH $defName")
      SearchResult(goal, BestFirstSearch(generator(goal), maxExpansions, focusFirstGoal, openGoalCost, maxDepth).search(initialProof) as? ArendProof)
    }

  /** Asserts that the search found a proof with no goals left that typechecks against the original goal. */
  fun assertProves(result: SearchResult, expectedProof: String) {
    assertEquals(expectedProof, assertProves(result))
  }

  /** Asserts that the search found a proof with no goals left that typechecks against the original goal, and returns it. */
  fun assertProves(result: SearchResult): String {
    val proof = assertNotNull(result.proof, "Search should find a proof")
    assertTrue(proof.isFinished(), "Proof should have no goals left: $proof")

    val term = assertNotNull(proof.getProof())
    val errorReporter = ListErrorReporter()
    val typechecker = CheckTypeVisitor.loadTypecheckingContext(result.goal.typechecker.saveTypecheckingContext(), errorReporter)
    val typed = typechecker.finalize(typechecker.typecheck(term, result.goal.expectedType), term)
    assertNotNull(typed, "Proof should typecheck: $proof")
    assertTrue(errorReporter.errorList.isEmpty(), "Proof should typecheck without errors or goals: ${errorReporter.errorList}")
    return proof.toString()
  }
}
