package integration

import search.best_first.BestFirstSearch
import typechecker.cli.*
import typechecker.cli.proofstep.CliLLMStepGenerator
import kotlin.test.Test
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import java.nio.file.Files
import java.nio.file.Paths

/**
 * End-to-end tests using the real Arend CLI + real LLM.
 *
 * All test definitions use custom functions (double, bnot, band, len, mymap, etc.)
 * on standard Arend types so the LLM cannot shortcut with library lemmas.
 *
 * Requirements:
 *   1. Arend CLI jar built at arend-lang-new/Arend/cli/build/libs/cli-*-full.jar
 *   2. arend-lib at arend-lang-new/Arend/arend-lib/
 *   3. VPN on, LITELLM_API_KEY env var set (for LLM tests)
 *
 * Run: ./gradlew test --tests "integration.CliLLMIntegrationTest" -DmaxAttempts=5
 */
class CliLLMIntegrationTest {

    private val libPath = Paths.get("/Users/admin/codingspace/arend-lang-new/Arend/arend-lib")
    private val maxAttempts = Integer.getInteger("maxAttempts", 10)

    private fun requireCli(): CliProcessApi? {
        if (!Files.exists(libPath.resolve("arend.yaml"))) {
            println("SKIP: arend-lib not found at $libPath")
            return null
        }
        val jarPath = Paths.get("/Users/admin/codingspace/arend-lang-new/Arend/cli/build/libs/cli-1.11.0-full.jar")
        if (!Files.exists(jarPath)) {
            println("SKIP: CLI jar not found at $jarPath")
            return null
        }
        return CliProcessApi(libPath, jarPath)
    }

    private fun requireLLM(): Boolean {
        val key = System.getenv("LITELLM_API_KEY")
        if (key.isNullOrEmpty()) {
            println("SKIP: LITELLM_API_KEY not set (VPN off?)")
            return false
        }
        return true
    }

    // ── CLI-only tests ──────────────────────────────────────────

    @Test
    fun `daemon - all test definitions have exactly 1 goal`() {
        val cli = requireCli() ?: return
        cli.use {
            val defs = listOf(
                "refl-zero", "suc-cong", "bnot-bnot", "band-comm", "bor-comm",
                "my-trans", "my-trans3", "double-plus", "double-add",
                "app-nil-right", "app-assoc", "len-app",
                "mymap-app", "mymap-comp", "mymap-id", "pair-eq"
            )
            for (def in defs) {
                val resp = it.findGoals("testPS:$def")
                println("$def: ${resp.goals.size} goal(s) — ${resp.goals.firstOrNull()?.expectedType ?: "?"}")
                assertTrue(resp.goals.size == 1, "testPS:$def should have exactly 1 goal")
            }
        }
    }

    @Test
    fun `daemon - checkExpression idp for refl-zero`() {
        val cli = requireCli() ?: return
        cli.use {
            val goals = it.findGoals("testPS:refl-zero").goals
            assertTrue(goals.isNotEmpty())
            val result = it.checkExpression("testPS:refl-zero", goals[0].id, "idp")
            println("checkExpression(idp) => success=${result.success}")
            assertTrue(result.success, "idp should typecheck for 0 = 0")
        }
    }

    @Test
    fun `daemon - applyStep idp for refl-zero completes proof`() {
        val cli = requireCli() ?: return
        cli.use {
            val goals = it.findGoals("testPS:refl-zero").goals
            assertTrue(goals.isNotEmpty())
            val result = it.applyStep("testPS:refl-zero", goals[0].id, "idp")
            println("applyStep(idp) => success=${result.success}, remaining=${result.goals.size}")
            assertTrue(result.success)
            assertTrue(result.goals.isEmpty())
        }
    }

    @Test
    fun `daemon - applyStep with case split creates subgoals`() {
        val cli = requireCli() ?: return
        cli.use {
            val goals = it.findGoals("testPS:bnot-bnot").goals
            assertTrue(goals.size == 1)

            val expr = """\case \elim b \with { | ff => {?} | tt => {?} }"""
            val result = it.applyStep("testPS:bnot-bnot", goals[0].id, expr)
            println("applyStep(case split) => success=${result.success}, remaining=${result.goals.size}")
            assertTrue(result.success, "case split should typecheck")
            assertTrue(result.goals.size == 2, "Should have 2 remaining goals after case split")
            for (g in result.goals) println("  Goal ${g.id}: ${g.expectedType}")
        }
    }

    @Test
    fun `daemon - applyStep with rewrite creates subgoal`() {
        val cli = requireCli() ?: return
        cli.use {
            val goals = it.findGoals("testPS:my-trans").goals
            assertTrue(goals.size == 1)

            val result = it.applyStep("testPS:my-trans", goals[0].id, "rewrite p {?}")
            println("applyStep(rewrite p {?}) => success=${result.success}, remaining=${result.goals.size}")
            assertTrue(result.success)
            assertTrue(result.goals.size == 1, "Should have 1 remaining goal after rewrite")
            println("  Remaining goal: ${result.goals[0].expectedType}")
        }
    }

    @Test
    fun `daemon - PlainTextProof initial + replaceGoal for refl-zero`() {
        val cli = requireCli() ?: return
        cli.use { d ->
            val proof = PlainTextProof.initial(d, "testPS:refl-zero")
            assertTrue(!proof.isFinished())

            val goal = proof.goals()[0]
            val replacement = PlainTextProof(d, "testPS:refl-zero", "idp")
            val result = proof.replaceGoal(goal, replacement)
            assertNotNull(result)
            assertTrue(result.isFinished())
        }
    }

    // ── LLM tests: single-step ────────────────────────────────────

    @Test
    fun `llm - solves refl-zero (idp)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:refl-zero"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
            assertTrue(result.isFinished())
        }
    }

    @Test
    fun `llm - solves suc-cong (pmap suc p)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:suc-cong"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
        }
    }

    // ── LLM tests: multi-step case split ──────────────────────────

    @Test
    fun `llm - solves bnot-bnot (3 BFS steps - case split + 2x idp)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:bnot-bnot"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - solves band-comm (5 BFS steps - case split + 4x idp)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:band-comm"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    // ── LLM tests: multi-step rewrite chains ──────────────────────

    @Test
    fun `llm - solves my-trans (2 BFS steps - rewrite + fill)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:my-trans"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - solves my-trans3 (3 BFS steps - rewrite chain)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:my-trans3"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    // ── LLM tests: multi-step induction ───────────────────────────

    @Test
    fun `llm - solves app-nil-right (induction on list)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:app-nil-right"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - solves mymap-id (induction on list)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:mymap-id"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - attempts double-plus (induction + arithmetic)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:double-plus"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - attempts len-app (induction + addition)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:len-app"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - attempts app-assoc (deep induction)`() {
        val cli = requireCli() ?: return
        if (!requireLLM()) return
        cli.use { d ->
            val moduleDef = "testPS:app-assoc"
            val proof = PlainTextProof.initial(d, moduleDef)
            println("=== LLM: $moduleDef === Goals: ${proof.goals()}")

            val result = BestFirstSearch(CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }
}
