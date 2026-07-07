package integration

import search.best_first.BestFirstSearch
import typechecker.cli.*
import typechecker.cli.proofstep.CliLLMStepGenerator
import kotlin.test.Test
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

/**
 * End-to-end tests using the real Arend CLI + real LLM.
 *
 * Each test creates its own testPS.ard with only the definitions it needs,
 * preventing goal contamination from other lemmas' {?} holes.
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
    private val testModulePath: Path = libPath.resolve("src/testPS.ard")
    private val testBinPath: Path = libPath.resolve("bin/testPS.arc")
    private val testSigPath: Path = libPath.resolve(".sig/testPS.ard")

    companion object {
        // ── Premises (signatures for LLM prompt) ──────────────────

        val PMAP = """\func pmap {A B : \Type} {a a' : A} (f : A -> B) (p : a = a') : f a = f a'"""
        val PMAP2 = """\func pmap2 {A B C : \Type} {a a' : A} {b b' : B} (f : A -> B -> C) (p : a = a') (q : b = b') : f a b = f a' b'"""
        val TRANSPORT = """\func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a) : B a'"""
        val INV = """\func inv {A : \Type} {a a' : A} (p : a = a') : a' = a"""
        val CONCAT = """\func *> {A : \Type} {a a' a'' : A} (p : a = a') (q : a' = a'') : a = a''"""
        val REWRITE = """\meta rewrite (p : a = b) (e : <goal with b>) : <goal with a> -- substitutes b for a in goal"""
        val EXT = """\meta ext -- proves equality of functions, sigma types, records"""

        val BOOL = """\data Bool | ff | tt"""
        val BNOT = """\func bnot (b : Bool) : Bool | ff => tt | tt => ff"""
        val BAND = """\func band (a b : Bool) : Bool \elim a | ff => ff | tt => b"""
        val BOR = """\func bor (a b : Bool) : Bool \elim a | ff => b | tt => tt"""
        val DOUBLE = """\func double (n : Nat) : Nat \elim n | 0 => 0 | suc n => suc (suc (double n))"""
        val LEN = """\func len {A : \Type} (l : List A) : Nat \elim l | nil => 0 | _ :: t => suc (len t)"""
        val MYMAP = """\func mymap {A B : \Type} (f : A -> B) (l : List A) : List B \elim l | nil => nil | a :: t => f a :: mymap f t"""
        val DIV_BASE = """\record DivBase {M : Monoid} (\coerce val : M) (elem inv : M)"""
        val LDIV = """\record LDiv \extends DivBase
                        | inv-right : val * inv = elem """
        val RDIV = """\record RInv \extends LDiv
                        | elem => ide"""
        val IRR = """\class Irr {M : CMonoid} (\coerce e : M) (notInv : Not (Inv e))
                        | isIrr {x y : M} : e = x * y -> Inv x || Inv y
                        | isCancelable-left {x y : M} : e * x = e * y -> x = y"""
        val INV_RECORD = """\record Inv \extends LInv, RInv"""
        val NAT_UNIT = """\lemma natUnit {n m : Nat} (p : n * m = 1) : m = 1"""
        val OR = """\truncated \data \infixr 2 || (A B : \Type) : \Prop
  | byLeft A
  | byRight B"""


        // ── Source definitions (fully implemented, for testPS.ard) ─

        val SRC_BOOL = """\data Bool | ff | tt"""

        val SRC_BNOT = """\func bnot (b : Bool) : Bool
  | ff => tt
  | tt => ff"""

        val SRC_BAND = """\func band (a b : Bool) : Bool \elim a
  | ff => ff
  | tt => b"""

        val SRC_BOR = """\func bor (a b : Bool) : Bool \elim a
  | ff => b
  | tt => tt"""

        val SRC_DOUBLE = """\func double (n : Nat) : Nat \elim n
  | 0 => 0
  | suc n => suc (suc (double n))"""

        val SRC_LEN = """\func len {A : \Type} (l : List A) : Nat \elim l
  | nil => 0
  | _ :: t => suc (len t)"""

        val SRC_MYMAP = """\func mymap {A B : \Type} (f : A -> B) (l : List A) : List B \elim l
  | nil => nil
  | a :: t => f a :: mymap f t"""

        // ── Target lemmas (with {?} body, for testPS.ard) ─────────

        val TARGET_REFL_ZERO = """\lemma refl-zero : 0 = 0
  => {?}"""

        val TARGET_SUC_CONG = """\lemma suc-cong (a b : Nat) (p : a = b) : suc a = suc b
  => {?}"""

        val TARGET_BNOT_BNOT = """\lemma bnot-bnot (b : Bool) : bnot (bnot b) = b
  => {?}"""

        val TARGET_BAND_COMM = """\lemma band-comm (a b : Bool) : band a b = band b a
  => {?}"""

        val TARGET_BOR_COMM = """\lemma bor-comm (a b : Bool) : bor a b = bor b a
  => {?}"""

        val TARGET_MY_TRANS = """\lemma my-trans {A : \Set} {a b c : A} (p : a = b) (q : b = c) : a = c
  => {?}"""

        val TARGET_MY_TRANS3 = """\lemma my-trans3 {A : \Set} {a b c d : A} (p : a = b) (q : b = c) (r : c = d) : a = d
  => {?}"""

        val TARGET_DOUBLE_PLUS = """\lemma double-plus (n : Nat) : double n = n + n
  => {?}"""

        val TARGET_DOUBLE_ADD = """\lemma double-add (n m : Nat) : double (n + m) = double n + double m
  => {?}"""

        val TARGET_APP_NIL_RIGHT = """\lemma app-nil-right {A : \Set} (l : List A) : l ++ nil = l
  => {?}"""

        val TARGET_APP_ASSOC = """\lemma app-assoc {A : \Set} (l1 l2 l3 : List A)
  : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
  => {?}"""

        val TARGET_LEN_APP = """\lemma len-app {A : \Set} (l1 l2 : List A)
  : len (l1 ++ l2) = len l1 + len l2
  => {?}"""

        val TARGET_MYMAP_APP = """\lemma mymap-app {A B : \Set} (f : A -> B) (l1 l2 : List A)
  : mymap f (l1 ++ l2) = mymap f l1 ++ mymap f l2
  => {?}"""

        val TARGET_MYMAP_COMP = """\lemma mymap-comp {A B C : \Set} (f : A -> B) (g : B -> C) (l : List A)
  : mymap g (mymap f l) = mymap (\lam a => g (f a)) l
  => {?}"""

        val TARGET_MYMAP_ID = """\lemma mymap-id {A : \Set} (l : List A) : mymap (\lam a => a) l = l
  => {?}"""

        val TARGET_PAIR_EQ = """\lemma pair-eq {A B : \Set} {a a' : A} {b b' : B}
  (p : a = a') (q : b = b') : (a, b) = (a', b')
  => {?}"""

        val TARGET_PRIME_CHAR_DIR = """\lemma prime-char-dir {n : Nat} (p : Irr n) {k : Nat} (k|n : LDiv k n) : (k = n) || (k = 1)
            => {?}"""

        val ALL_SOURCES = listOf(SRC_DOUBLE, SRC_LEN, SRC_MYMAP, SRC_BOOL, SRC_BNOT, SRC_BAND, SRC_BOR)
        val ALL_TARGETS = listOf(
            TARGET_REFL_ZERO, TARGET_SUC_CONG, TARGET_BNOT_BNOT, TARGET_BAND_COMM,
            TARGET_BOR_COMM, TARGET_MY_TRANS, TARGET_MY_TRANS3, TARGET_DOUBLE_PLUS,
            TARGET_DOUBLE_ADD, TARGET_APP_NIL_RIGHT, TARGET_APP_ASSOC, TARGET_LEN_APP,
            TARGET_MYMAP_APP, TARGET_MYMAP_COMP, TARGET_MYMAP_ID, TARGET_PAIR_EQ
        )
    }

    // ── Helpers ────────────────────────────────────────────────────

    private fun requireCli(): CliApi? {
        if (!Files.exists(libPath.resolve("arend.yaml"))) {
            println("SKIP: arend-lib not found at $libPath")
            return null
        }
        try {
            val conn = CliConnection(libPath)
            println("Using daemon connection")
            return conn
        } catch (_: Exception) {}
        val jarPath = Paths.get("/Users/admin/codingspace/arend-lang-new/Arend/cli/build/libs/cli-1.11.0-full.jar")
        if (!Files.exists(jarPath)) {
            println("SKIP: CLI jar not found at $jarPath")
            return null
        }
        println("Using CLI process (no daemon running — will be slow)")
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

    private fun writeTestModule(blocks: List<String>) {
        val content = buildString {
            appendLine("""\import Algebra.Monoid""")
            appendLine("""\import Algebra.Monoid.Prime""")
            appendLine("""\import Arith.Nat""")
            appendLine("""\import Logic""")
            appendLine("""\import Data.List""")
            appendLine("""\import Meta""")
            appendLine("""\import Paths""")
            appendLine("""\import Paths.Meta""")
            appendLine("""\import Function.Meta""")
            appendLine("""\open Nat""")
            appendLine("""\open Monoid (LDiv, Inv)""")
            for (block in blocks) {
                appendLine()
                appendLine(block)
            }
        }
        Files.writeString(testModulePath, content)
        Files.deleteIfExists(testBinPath)
        Files.deleteIfExists(testSigPath)
    }

    private fun cleanTestModule() {
        Files.deleteIfExists(testModulePath)
        Files.deleteIfExists(testBinPath)
        Files.deleteIfExists(testSigPath)
    }

    private fun withTestModule(blocks: List<String>, test: (CliApi) -> Unit) {
        writeTestModule(blocks)
        try {
            val cli = requireCli() ?: return
            try {
                test(cli)
            } finally {
                (cli as? AutoCloseable)?.close()
            }
        } finally {
            cleanTestModule()
        }
    }

    private fun searchFrom(cli: CliApi, moduleDef: String, premises: List<String>, body: String): PlainTextProof {
        val response = cli.applyStep(moduleDef, body)
        assertTrue(response.success, "Partial proof should typecheck: ${response.errors}")
        assertTrue(response.goals.isNotEmpty(), "Partial proof should have goals")
        val goals = response.goals.map { PlainTextGoal(it.id, it.expectedType, it.context, moduleDef) }
        val proof = PlainTextProof(cli, moduleDef, body, goals)
        println("Starting from partial proof: $body")
        println("  ${goals.size} goal(s): ${goals.map { it.expectedType }}")
        val gen = CliLLMStepGenerator(cli, moduleDef, premises, maxAttempts = maxAttempts)
        val result = BestFirstSearch(gen).search(proof)
        assertNotNull(result, "Search should find a proof")
        assertTrue(result.isFinished(), "Proof should be complete")
        println("FOUND: $result")
        return result as PlainTextProof
    }

    // ── CLI-only tests ──────────────────────────────────────────

    @Test
    fun `daemon - signatureInfo for isIrr has propositional param`() {
        withTestModule(listOf(TARGET_PRIME_CHAR_DIR)) { cli ->
            val info = cli.signatureInfo("testPS:prime-char-dir", "isIrr")
            assertNotNull(info, "signatureInfo should return result for isIrr")
            println("isIrr signature: $info")
            println("  params: ${info.params.map { "${it.name}:${it.type} explicit=${it.explicit} prop=${it.propositional}" }}")
            val explicitParams = info.params.filter { it.explicit }
            assertTrue(explicitParams.isNotEmpty(), "isIrr should have at least one explicit param")
            val propParam = explicitParams.find { it.propositional }
            assertNotNull(propParam, "isIrr should have a propositional explicit param (the equality)")
            println("  propositional param: ${propParam.name} : ${propParam.type}")
        }
    }

    @Test
    fun `daemon - buildCaseExpression on isIrr result with infix Or type`() {
        withTestModule(listOf(TARGET_PRIME_CHAR_DIR)) { cli ->
            val goals = cli.findGoals("testPS:prime-char-dir").goals
            assertTrue(goals.isNotEmpty())
            val goal = PlainTextGoal(goals[0].id, goals[0].expectedType, goals[0].context, "testPS:prime-char-dir")

            val gen = CliLLMStepGenerator(cli, "testPS:prime-char-dir", listOf(OR, IRR, LDIV, INV), maxAttempts = 1)
            val caseExpr = gen.buildCaseExpression("p.isIrr (inv k|n.inv-right)", goal)
            println("buildCaseExpression result: $caseExpr")
            assertNotNull(caseExpr, "Should build case expression for isIrr result")
            assertTrue(caseExpr.contains("byLeft"), "Should have byLeft constructor")
            assertTrue(caseExpr.contains("byRight"), "Should have byRight constructor")
            assertTrue(caseExpr.contains("\\case"), "Should be a \\case expression (not a variable)")
        }
    }

    @Test
    fun `daemon - all test definitions have exactly 1 goal`() {
        withTestModule(ALL_SOURCES + ALL_TARGETS) { cli ->
            val defs = listOf(
                "refl-zero", "suc-cong", "bnot-bnot", "band-comm", "bor-comm",
                "my-trans", "my-trans3", "double-plus", "double-add",
                "app-nil-right", "app-assoc", "len-app",
                "mymap-app", "mymap-comp", "mymap-id", "pair-eq"
            )
            for (def in defs) {
                val resp = cli.findGoals("testPS:$def")
                println("$def: ${resp.goals.size} goal(s) — ${resp.goals.firstOrNull()?.expectedType ?: "?"}")
                assertTrue(resp.goals.size == 1, "testPS:$def should have exactly 1 goal")
            }
        }
    }

    @Test
    fun `daemon - applyStep idp for refl-zero completes proof`() {
        withTestModule(listOf(TARGET_REFL_ZERO)) { cli ->
            val result = cli.applyStep("testPS:refl-zero", "idp")
            println("applyStep(idp) => success=${result.success}, remaining=${result.goals.size}")
            assertTrue(result.success)
            assertTrue(result.goals.isEmpty())
        }
    }

    @Test
    fun `daemon - applyStep with case split creates subgoals`() {
        withTestModule(listOf(SRC_BOOL, SRC_BNOT, TARGET_BNOT_BNOT)) { cli ->
            val expr = """\case \elim b \with { | ff => {?} | tt => {?} }"""
            val result = cli.applyStep("testPS:bnot-bnot", expr)
            println("applyStep(case split) => success=${result.success}, remaining=${result.goals.size}")
            assertTrue(result.success, "case split should typecheck")
            assertTrue(result.goals.size == 2, "Should have 2 remaining goals after case split")
            for (g in result.goals) println("  Goal ${g.id}: ${g.expectedType}")
        }
    }

    @Test
    fun `daemon - applyStep with top-level elim solves double-plus`() {
        withTestModule(listOf(SRC_DOUBLE, TARGET_DOUBLE_PLUS)) { cli ->
            val expr = """\elim n | 0 => idp | suc n => pmap (\lam x => suc (suc x)) (double-plus n)"""
            val result = cli.applyStep("testPS:double-plus", expr)
            println("applyStep(elim double-plus) => success=${result.success}, goals=${result.goals.size}, errors=${result.errors}")
            assertTrue(result.success, "top-level \\elim should typecheck")
            assertTrue(result.goals.isEmpty(), "Should have no remaining goals")
        }
    }

    @Test
    fun `daemon - applyStep with top-level elim and goals`() {
        withTestModule(listOf(SRC_DOUBLE, TARGET_DOUBLE_PLUS)) { cli ->
            val expr = """\elim n | 0 => idp | suc n => {?}"""
            val result = cli.applyStep("testPS:double-plus", expr)
            println("applyStep(elim with goal) => success=${result.success}, goals=${result.goals.size}")
            assertTrue(result.success, "top-level \\elim with goal should typecheck")
            assertTrue(result.goals.size == 1, "Should have 1 remaining goal")
            println("  Remaining goal: ${result.goals[0].expectedType}")
        }
    }

    @Test
    fun `daemon - applyStep with rewrite creates subgoal`() {
        withTestModule(listOf(TARGET_MY_TRANS)) { cli ->
            val result = cli.applyStep("testPS:my-trans", "rewrite p {?}")
            println("applyStep(rewrite p {?}) => success=${result.success}, remaining=${result.goals.size}")
            assertTrue(result.success)
            assertTrue(result.goals.size == 1, "Should have 1 remaining goal after rewrite")
            println("  Remaining goal: ${result.goals[0].expectedType}")
        }
    }

    @Test
    fun `daemon - PlainTextProof initial + replaceGoal for refl-zero`() {
        withTestModule(listOf(TARGET_REFL_ZERO)) { cli ->
            val proof = PlainTextProof.initial(cli, "testPS:refl-zero")
            assertTrue(!proof.isFinished())

            val goal = proof.goals()[0]
            val replacement = PlainTextProof(cli, "testPS:refl-zero", "idp")
            val result = proof.replaceGoal(goal, replacement)
            assertNotNull(result)
            assertTrue(result.isFinished())
        }
    }

    // ── LLM: single-step (LLM solves in one call) ────────────────

    @Test
    fun `llm - single-step - refl-zero`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_REFL_ZERO)) { d ->
            val moduleDef = "testPS:refl-zero"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
            assertTrue(result.isFinished())
        }
    }

    @Test
    fun `llm - single-step - suc-cong`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_SUC_CONG)) { d ->
            val moduleDef = "testPS:suc-cong"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
        }
    }

    @Test
    fun `llm - single-step - bnot-bnot`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_BOOL, SRC_BNOT, TARGET_BNOT_BNOT)) { d ->
            val moduleDef = "testPS:bnot-bnot"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(BOOL, BNOT), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
        }
    }

    @Test
    fun `llm - single-step - band-comm`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_BOOL, SRC_BAND, TARGET_BAND_COMM)) { d ->
            val moduleDef = "testPS:band-comm"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(BOOL, BAND), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
        }
    }

    @Test
    fun `llm - single-step - my-trans`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_MY_TRANS)) { d ->
            val moduleDef = "testPS:my-trans"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(REWRITE, CONCAT, INV), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
        }
    }

    @Test
    fun `llm - single-step - pair-eq`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_PAIR_EQ)) { d ->
            val moduleDef = "testPS:pair-eq"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP2, EXT), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
            assertNotNull(result)
        }
    }

    // ── LLM: multi-step (start from partial proof with {?} holes) ─

    @Test
    fun `llm - multi-step - bnot-bnot from case split`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_BOOL, SRC_BNOT, TARGET_BNOT_BNOT)) { d ->
            searchFrom(d, "testPS:bnot-bnot", listOf(BOOL, BNOT),
                """\case \elim b \with { | ff => {?} | tt => {?} }""")
        }
    }

    @Test
    fun `llm - multi-step - band-comm from case split`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_BOOL, SRC_BAND, TARGET_BAND_COMM)) { d ->
            searchFrom(d, "testPS:band-comm", listOf(BOOL, BAND),
                """\case \elim a, \elim b \with { | ff, ff => {?} | ff, tt => {?} | tt, ff => {?} | tt, tt => {?} }""")
        }
    }

    @Test
    fun `llm - multi-step - my-trans3 from rewrite`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_MY_TRANS3)) { d ->
            searchFrom(d, "testPS:my-trans3", listOf(REWRITE, CONCAT, INV),
                "rewrite p {?}")
        }
    }

    @Test
    fun `llm - multi-step - double-plus from elim skeleton`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_DOUBLE, TARGET_DOUBLE_PLUS)) { d ->
            searchFrom(d, "testPS:double-plus", listOf(PMAP, DOUBLE),
                """\elim n | 0 => {?} | suc n => {?}""")
        }
    }

    @Test
    fun `llm - multi-step - app-nil-right from elim skeleton`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_APP_NIL_RIGHT)) { d ->
            searchFrom(d, "testPS:app-nil-right", listOf(PMAP),
                """\elim l | nil => {?} | :: a t => {?}""")
        }
    }

    @Test
    fun `llm - multi-step - mymap-id from elim skeleton`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_MYMAP, TARGET_MYMAP_ID)) { d ->
            searchFrom(d, "testPS:mymap-id", listOf(PMAP, MYMAP),
                """\elim l | nil => {?} | :: a t => {?}""")
        }
    }

    @Test
    fun `llm - multi-step - len-app from elim skeleton`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_LEN, TARGET_LEN_APP)) { d ->
            searchFrom(d, "testPS:len-app", listOf(PMAP, LEN),
                """\elim l1 | nil => {?} | :: a t => {?}""")
        }
    }

    // ── LLM: full search (from scratch, may need multiple steps) ──

    @Test
    fun `llm - full - double-plus`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_DOUBLE, TARGET_DOUBLE_PLUS)) { d ->
            val moduleDef = "testPS:double-plus"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP, DOUBLE), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - full - app-assoc`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_APP_ASSOC)) { d ->
            val moduleDef = "testPS:app-assoc"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - full - len-app`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_LEN, TARGET_LEN_APP)) { d ->
            val moduleDef = "testPS:len-app"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP, LEN), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - full - mymap-comp`() {
        if (!requireLLM()) return
        withTestModule(listOf(SRC_MYMAP, TARGET_MYMAP_COMP)) { d ->
            val moduleDef = "testPS:mymap-comp"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP, MYMAP), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }

    @Test
    fun `llm - full - prime-char-dir`() {
        if (!requireLLM()) return
        withTestModule(listOf(TARGET_PRIME_CHAR_DIR)) { d ->
            val moduleDef = "testPS:prime-char-dir"
            val proof = PlainTextProof.initial(d, moduleDef)
            val gen = CliLLMStepGenerator(d, moduleDef, listOf(PMAP, CONCAT, OR, IRR, INV_RECORD, NAT_UNIT, LDIV, RDIV, INV, DIV_BASE), maxAttempts = maxAttempts)
            val result = BestFirstSearch(gen).search(proof)
            println(if (result != null) "FOUND: $result" else "NOT FOUND")
        }
    }
}
