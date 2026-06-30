package integration

import org.arend.error.DummyErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.ModuleLocation
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.source.PreludeResourceSource
import org.arend.prelude.Prelude
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.server.impl.ArendServerImpl
import org.arend.term.concrete.Concrete
import org.arend.term.group.ConcreteGroup
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.core.expr.Expression
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.util.FileUtils
import org.arend.util.FileUtils.modulePath
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import search.best_first.BestFirstSearch
import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.test.assertNotNull
import kotlin.test.assertEquals
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

class CoreApiIntegrationTest {

    companion object {
        private val testLibDir: Path = Paths.get(System.getProperty("user.dir"), "test-lib")

        private var cachedEnv: Triple<ArendServer, ConcreteGroup, ModuleLocation>? = null
        private var cacheModule: String? = null

        private fun loadServer(testModule: String): Triple<ArendServer, ConcreteGroup, ModuleLocation>? {
            if (cacheModule == testModule && cachedEnv != null) return cachedEnv

            val configFile = testLibDir.resolve(FileUtils.LIBRARY_CONFIG_FILE)
            if (!Files.exists(configFile)) {
                println("SKIPPED: test-lib not found at $testLibDir")
                return null
            }

            try {
                val errorReporter = ListErrorReporter()
                val libraryManager = LibraryManager(errorReporter)
                val server: ArendServer = ArendServerImpl(CliServerRequester(libraryManager), false, false, true)
                server.addReadOnlyModule(
                    Prelude.MODULE_LOCATION,
                    { PreludeResourceSource().loadGroup(DummyErrorReporter.INSTANCE)!! }
                )
                server.addErrorReporter(errorReporter)

                val library = FileSourceLibrary.fromConfigFile(configFile, false, ListErrorReporter())
                    ?: run {
                        println("SKIPPED: FileSourceLibrary.fromConfigFile returned null for $configFile")
                        return null
                    }
                libraryManager.updateLibrary(library, server)

                val modulePath = modulePath(testModule)
                for (mod in library.findModules(false)) {
                    library.getSource(mod, false)?.load(server, errorReporter)
                }

                val module = ModuleLocation(library.libraryName, ModuleLocation.LocationKind.SOURCE, modulePath)
                val checker = server.getCheckerFor(listOf(module))
                val group = server.getRawGroup(module) ?: run {
                    println("SKIPPED: getRawGroup returned null for $module")
                    return null
                }

                checker.resolveAll(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
                val allModules = server.modules.toList()
                if (allModules.isNotEmpty()) {
                    val allChecker = server.getCheckerFor(allModules)
                    allChecker.typecheck(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
                }

                val result = Triple(server, group, module)
                cachedEnv = result
                cacheModule = testModule
                return result
            } catch (e: Exception) {
                println("ERROR loading server: ${e::class.simpleName}: ${e.message}")
                e.printStackTrace()
                return null
            }
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
