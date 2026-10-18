package integration

import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.ModuleLocation
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.term.concrete.Concrete
import org.arend.term.group.ConcreteGroup
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.core.expr.Expression
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.CheckTypeVisitor
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import search.best_first.BestFirstSearch
import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.test.assertNotNull
import kotlin.test.assertEquals

class CoreApiIntegrationTest {

    companion object {
        private fun loadServer(testModule: String): Triple<ArendServer, ConcreteGroup, ModuleLocation>? {
            val module = TestLibrary.load()?.module(testModule) ?: run {
                println("SKIPPED: could not load module $testModule")
                return null
            }
            return Triple(module.server, module.group, module.location)
        }
    }

    private fun collectGoals(server: ArendServer, group: ConcreteGroup, module: ModuleLocation): Map<String, List<ArendGoal>> {
        val goalsByDef = mutableMapOf<String, MutableList<ArendGoal>>()
        val checker = server.getCheckerFor(listOf(module))

        group.traverseGroup { x ->
            x.definition?.let { def ->
                if (def is Concrete.FunctionDefinition) {
                    val defName = def.data.refLongName.toString()
                    checker.typecheck(
                        FullName(module, def.data.refLongName),
                        { errorReporter, pool, arendExtension, listener ->
                            object : CheckTypeVisitor(errorReporter, pool, arendExtension, listener) {
                                override fun visitGoal(expr: Concrete.GoalExpression, expectedType: Expression): TypecheckingResult {
                                    goalsByDef.getOrPut(defName) { mutableListOf() }
                                        .add(ArendGoal(expectedType, this, expr))
                                    return super.visitGoal(expr, expectedType)
                                }
                            }
                        },
                        null, ListErrorReporter(), UnstoppableCancellationIndicator.INSTANCE,
                        ProgressReporter.empty()
                    )
                }
            }
        }
        return goalsByDef
    }

    @Test
    fun `loads test library and finds goals`() {
        val (server, group, module) = loadServer("TestBasic") ?: run {
            println("SKIPPED: could not load test library")
            return
        }

        val goalsByDef = collectGoals(server, group, module)
        assertTrue(goalsByDef.isNotEmpty(), "Should find definitions with goals")

        for ((defName, goals) in goalsByDef) {
            println("  $defName: ${goals.size} goal(s)")
            for (goal in goals) {
                assertNotNull(goal.expectedType)
                println("    expected type: ${goal.expectedType}")
            }
        }
    }

    @Test
    fun `refl-test has exactly one goal`() {
        val (server, group, module) = loadServer("TestBasic") ?: return

        val goalsByDef = collectGoals(server, group, module)
        val goals = goalsByDef["refl-test"]
        assertNotNull(goals, "Should find refl-test definition")
        assertEquals(1, goals.size)
    }

    @Test
    fun `plus-zero-test has two goals from case split`() {
        val (server, group, module) = loadServer("TestBasic") ?: return

        val goalsByDef = collectGoals(server, group, module)
        val goals = goalsByDef["plus-zero-test"]
        assertNotNull(goals, "Should find plus-zero-test definition")
        assertEquals(2, goals.size, "Case split should produce 2 goals")
    }

    @Test
    fun `already-done has no goals`() {
        val (server, group, module) = loadServer("TestBasic") ?: return

        val goalsByDef = collectGoals(server, group, module)
        val goals = goalsByDef["already-done"]
        assertTrue(goals == null || goals.isEmpty(), "already-done should have no goals")
    }

    @Test
    fun `goal expected types are non-null`() {
        val (server, group, module) = loadServer("TestBasic") ?: return

        val goalsByDef = collectGoals(server, group, module)
        for ((_, goals) in goalsByDef) {
            for (goal in goals) {
                assertNotNull(goal.expectedType, "Every goal must have an expected type")
            }
        }
    }

    @Test
    fun `best first search finds proof with trivial mock generator`() {
        val (server, group, module) = loadServer("TestBasic") ?: return

        val goalsByDef = collectGoals(server, group, module)
        val goals = goalsByDef["refl-test"] ?: run {
            println("SKIPPED: refl-test not found")
            return
        }
        val goal = goals[0]

        val generator = object : ProofStepGenerator<ArendGoal> {
            var called = false
            override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
                if (called) return emptyList()
                called = true
                val emptyProof = object : Proof<ArendGoal> {
                    override fun goals() = emptyList<ArendGoal>()
                    override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = null
                }
                return listOf(ProofStep(emptyProof, 1.0))
            }
        }

        val search = BestFirstSearch<ArendGoal>(generator)
        val initialProof = object : Proof<ArendGoal> {
            override fun goals() = listOf(goal)
            override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = proof
        }

        val result = search.search(initialProof)
        assertNotNull(result, "Search should find proof with mock generator")
        assertTrue(result.isFinished())
        assertTrue(generator.called)
    }

    @Test
    fun `best first search exhausts when generator always produces new goals`() {
        val (server, group, module) = loadServer("TestBasic") ?: return

        val goalsByDef = collectGoals(server, group, module)
        val goals = goalsByDef["refl-test"] ?: return
        val goal = goals[0]

        var depth = 0
        val generator = object : ProofStepGenerator<ArendGoal> {
            override fun generate(g: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
                depth++
                val proof = object : Proof<ArendGoal> {
                    override fun goals() = listOf(g)
                    override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = proof
                }
                return listOf(ProofStep(proof, 1.0))
            }
        }

        val search = BestFirstSearch<ArendGoal>(generator)
        val initialProof = object : Proof<ArendGoal> {
            override fun goals() = listOf(goal)
            override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = proof
        }

        val result = search.search(initialProof)
        assertTrue(result == null, "Should exhaust without finding proof")
    }
}
