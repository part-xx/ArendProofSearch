package typechecker.cli

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class FakeCli : CliApi {
    var findGoalsResult: FindGoalsResponse = FindGoalsResponse("M:D", emptyList())
    var applyStepResult: ApplyStepResponse = ApplyStepResponse(false)
    var scopeResult: ScopeResponse = ScopeResponse()
    var proofSearchResult: ProofSearchResponse = ProofSearchResponse()
    val signatureInfoResults = mutableMapOf<String, SignatureInfoResponse>()

    val findGoalsCalls = mutableListOf<String>()
    val applyStepCalls = mutableListOf<Pair<String, String>>()

    override fun findGoals(moduleDef: String): FindGoalsResponse {
        findGoalsCalls.add(moduleDef)
        return findGoalsResult
    }

    override fun applyStep(moduleDef: String, fullBody: String): ApplyStepResponse {
        applyStepCalls.add(Pair(moduleDef, fullBody))
        return applyStepResult
    }

    override fun getScope(moduleDef: String, goalId: String): ScopeResponse {
        return scopeResult
    }

    override fun proofSearch(pattern: String): ProofSearchResponse {
        return proofSearchResult
    }

    override fun signature(moduleDef: String): String {
        return ""
    }

    override fun signatureInfo(moduleDef: String, name: String): SignatureInfoResponse? {
        return signatureInfoResults[name]
    }

    /** Per-expression scripted typeExpr responses; expressions not present return null. */
    val typeExprResponses = mutableMapOf<String, TypeExprResponse>()
    val typeExprCalls = mutableListOf<String>()

    override fun typeExpr(moduleDef: String, goalId: String, expression: String, proofBody: String?): TypeExprResponse? {
        typeExprCalls.add(expression)
        return typeExprResponses[expression]
    }
}

/** LLM client that returns a fixed sequence of responses, for testing generate(). */
class ScriptedLLMClient(responses: List<String>) : typechecker.LLMClient {
    private val queue = ArrayDeque(responses)
    val prompts = mutableListOf<String>()

    override suspend fun generateResponse(systemPrompt: String, userPrompt: String, temperature: Double?): String {
        prompts.add(userPrompt)
        return queue.removeFirst()
    }
}

class PlainTextProofTest {

    @Test
    fun `goals returns cached goals when provided`() {
        val cli = FakeCli()
        val cachedGoals = listOf(
            PlainTextGoal("0", "Nat", emptyList(), "M:D"),
            PlainTextGoal("1", "Bool", emptyList(), "M:D")
        )
        val proof = PlainTextProof(cli, "M:D", "{?}", cachedGoals)

        val goals = proof.goals()
        assertEquals(2, goals.size)
        assertEquals("0", goals[0].id)
        assertEquals("1", goals[1].id)
        assertTrue(cli.findGoalsCalls.isEmpty())
    }

    @Test
    fun `goals calls cli when no cached goals`() {
        val cli = FakeCli()
        cli.findGoalsResult = FindGoalsResponse(
            "M:D",
            listOf(
                GoalInfo("0", "", "a = b", listOf(ContextBinding("a", "Nat"), ContextBinding("b", "Nat"))),
                GoalInfo("1", "", "Nat", emptyList())
            )
        )
        val proof = PlainTextProof(cli, "M:D", "{?}")

        val goals = proof.goals()
        assertEquals(2, goals.size)
        assertEquals("a = b", goals[0].expectedType)
        assertEquals(2, goals[0].contextBindings.size)
        assertEquals("Nat", goals[1].expectedType)
        assertEquals(1, cli.findGoalsCalls.size)
        assertEquals("M:D", cli.findGoalsCalls[0])
    }

    @Test
    fun `goals maps GoalInfo fields correctly`() {
        val cli = FakeCli()
        cli.findGoalsResult = FindGoalsResponse(
            "TestMod:myFunc",
            listOf(GoalInfo("3", "goal3", "x + y = y + x", listOf(ContextBinding("x", "Nat"))))
        )
        val proof = PlainTextProof(cli, "TestMod:myFunc", "{?}")

        val goal = proof.goals()[0]
        assertEquals("3", goal.id)
        assertEquals("x + y = y + x", goal.expectedType)
        assertEquals(1, goal.contextBindings.size)
        assertEquals("x", goal.contextBindings[0].name)
        assertEquals("Nat", goal.contextBindings[0].type)
        assertEquals("TestMod:myFunc", goal.moduleDef)
    }

    @Test
    fun `replaceGoal returns null for non-PlainTextProof argument`() {
        val cli = FakeCli()
        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(PlainTextGoal("0", "Nat", emptyList(), "M:D")))
        val goal = proof.goals()[0]

        val otherProof = object : typechecker.Proof<PlainTextGoal> {
            override fun goals() = emptyList<PlainTextGoal>()
            override fun replaceGoal(goal: PlainTextGoal, proof: typechecker.Proof<PlainTextGoal>) = null
        }

        val result = proof.replaceGoal(goal, otherProof)
        assertNull(result)
    }

    @Test
    fun `replaceGoal returns null when cli reports failure`() {
        val cli = FakeCli()
        cli.applyStepResult = ApplyStepResponse(success = false, errors = listOf("Type mismatch"))

        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(PlainTextGoal("0", "Nat", emptyList(), "M:D")))
        val goal = proof.goals()[0]
        val replacement = PlainTextProof(cli, "M:D", "idp")

        val result = proof.replaceGoal(goal, replacement)
        assertNull(result)
    }

    @Test
    fun `replaceGoal returns new proof on success`() {
        val cli = FakeCli()
        cli.applyStepResult = ApplyStepResponse(
            success = true,
            proof = "rewrite p {?}",
            goals = listOf(GoalInfo("0", "", "b = b", emptyList()))
        )

        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(PlainTextGoal("0", "a = b", emptyList(), "M:D")))
        val goal = proof.goals()[0]
        val replacement = PlainTextProof(cli, "M:D", "rewrite p {?}")

        val result = proof.replaceGoal(goal, replacement)
        assertNotNull(result)
        val newProof = result as PlainTextProof
        assertEquals("rewrite p {?}", newProof.proofText)
        assertEquals(1, newProof.goals().size)
        assertEquals("b = b", newProof.goals()[0].expectedType)
    }

    @Test
    fun `replaceGoal passes correct arguments to cli`() {
        val cli = FakeCli()
        cli.applyStepResult = ApplyStepResponse(success = true, proof = "idp", goals = emptyList())

        val proof = PlainTextProof(cli, "TestMod:lemma1", "{?}",
            listOf(PlainTextGoal("0", "Nat", emptyList(), "TestMod:lemma1")))
        val goal = proof.goals()[0]
        val replacement = PlainTextProof(cli, "TestMod:lemma1", "idp")

        proof.replaceGoal(goal, replacement)

        assertEquals(1, cli.applyStepCalls.size)
        assertEquals("TestMod:lemma1", cli.applyStepCalls[0].first)
        assertEquals("idp", cli.applyStepCalls[0].second)
    }

    @Test
    fun `replaceGoal returns finished proof when cli reports no remaining goals`() {
        val cli = FakeCli()
        cli.applyStepResult = ApplyStepResponse(success = true, proof = "idp", goals = emptyList())

        val proof = PlainTextProof(cli, "M:D", "{?}",
            listOf(PlainTextGoal("0", "0 = 0", emptyList(), "M:D")))
        val goal = proof.goals()[0]
        val replacement = PlainTextProof(cli, "M:D", "idp")

        val result = proof.replaceGoal(goal, replacement)
        assertNotNull(result)
        assertTrue(result.isFinished())
    }

    @Test
    fun `initial factory method creates proof with goals from cli`() {
        val cli = FakeCli()
        cli.findGoalsResult = FindGoalsResponse(
            "M:D",
            listOf(
                GoalInfo("0", "", "Nat", emptyList()),
                GoalInfo("1", "", "Bool", emptyList())
            )
        )

        val proof = PlainTextProof.initial(cli, "M:D")
        assertEquals("{?}", proof.proofText)
        assertEquals(2, proof.goals().size)
        assertTrue(cli.findGoalsCalls.isEmpty() || cli.findGoalsCalls.size == 1)
    }

    @Test
    fun `toString returns proofText`() {
        val cli = FakeCli()
        val proof = PlainTextProof(cli, "M:D", "rewrite p idp")
        assertEquals("rewrite p idp", proof.toString())
    }

    @Test
    fun `isFinished returns true when no goals`() {
        val cli = FakeCli()
        val proof = PlainTextProof(cli, "M:D", "idp", emptyList())
        assertTrue(proof.isFinished())
    }

    @Test
    fun `isFinished returns false when goals exist`() {
        val cli = FakeCli()
        val proof = PlainTextProof(cli, "M:D", "{?}",
            listOf(PlainTextGoal("0", "Nat", emptyList(), "M:D")))
        assertTrue(!proof.isFinished())
    }
}

class StepParsingTest {
    private fun makeGenerator(): typechecker.cli.proofstep.CliLLMStepGenerator {
        val cli = FakeCli()
        return typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D")
    }

    @Test
    fun `parseStepFromResponse extracts APPLY step`() {
        val gen = makeGenerator()
        val response = """
            Plan: Apply pmap with identity function.
            [APPLY pmap]
            \lam x => x
            [/APPLY]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("apply", step.type)
        assertEquals("pmap", step.name)
        assertEquals(1, step.args.size)
        assertEquals("\\lam x => x", step.args[0])
    }

    @Test
    fun `parseStepFromResponse extracts APPLY with no args`() {
        val gen = makeGenerator()
        val response = """
            Plan: Apply byLeft.
            [APPLY byLeft]
            [/APPLY]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("apply", step.type)
        assertEquals("byLeft", step.name)
        assertTrue(step.args.isEmpty())
    }

    @Test
    fun `parseStepFromResponse extracts REWRITE step`() {
        val gen = makeGenerator()
        val response = """
            Plan: Rewrite using p.
            [REWRITE]p[/REWRITE]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("rewrite", step.type)
        assertEquals("p", step.rawTerm)
    }

    @Test
    fun `parseStepFromResponse extracts REWRITE with complex equality`() {
        val gen = makeGenerator()
        val response = """
            Plan: Rewrite using inv q.
            [REWRITE]inv q[/REWRITE]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("rewrite", step.type)
        assertEquals("inv q", step.rawTerm)
    }

    @Test
    fun `parseStepFromResponse extracts REFINE step`() {
        val gen = makeGenerator()
        val response = """
            Plan: The goal is a pair, give it as a term with holes.
            [REFINE](mod-lem p {?}, rec-lem p {?})[/REFINE]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("refine", step.type)
        assertEquals("(mod-lem p {?}, rec-lem p {?})", step.rawTerm)
    }

    @Test
    fun `parseStepFromResponse extracts multi-line REFINE step`() {
        val gen = makeGenerator()
        val response = """
            [REFINE]\case \elim n, p \with {
              | 0, p => {?}
              | suc n, p => {?}
            }[/REFINE]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("refine", step.type)
        assertTrue(step.rawTerm!!.startsWith("\\case \\elim n, p \\with {"))
    }

    @Test
    fun `parseStepFromResponse extracts CASE step`() {
        val gen = makeGenerator()
        val response = """
            Plan: Case split on n.
            [CASE]n[/CASE]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("case", step.type)
        assertEquals("n", step.rawTerm)
    }

    @Test
    fun `parseStepFromResponse extracts INTRO with names`() {
        val gen = makeGenerator()
        val response = """
            Plan: Introduce x and y.
            [INTRO]x y[/INTRO]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("intro", step.type)
        assertEquals(listOf("x", "y"), step.args)
    }

    @Test
    fun `parseStepFromResponse extracts INTRO with no names`() {
        val gen = makeGenerator()
        val response = """
            Plan: Introduce.
            [INTRO][/INTRO]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("intro", step.type)
        assertTrue(step.args.isEmpty())
    }

    @Test
    fun `parseStepFromResponse returns null for no tags`() {
        val gen = makeGenerator()
        val step = gen.parseStepFromResponse("Just some text without tags")
        assertNull(step)
    }

    @Test
    fun `buildTermFromApply constructs term with prop args as holes`() {
        val gen = makeGenerator()
        // Manually populate the cache via reflection or by using a real test
        // For now, test the logic directly
        val info = SignatureInfoResponse(
            name = "pmap",
            params = listOf(
                ParamInfo("A", "\\Type", false, false),
                ParamInfo("B", "\\Type", false, false),
                ParamInfo("f", "A -> B", true, false),
                ParamInfo("a", "A", false, false),
                ParamInfo("a'", "A", false, false),
                ParamInfo("p", "a = a'", true, true)
            ),
            resultType = "f a = f a'"
        )
        // Use reflection to populate cache
        val cacheField = gen.javaClass.getDeclaredField("sigInfoCache")
        cacheField.isAccessible = true
        @Suppress("UNCHECKED_CAST")
        val cache = cacheField.get(gen) as MutableMap<String, SignatureInfoResponse>
        cache["pmap"] = info

        val term = gen.buildTermFromApply("pmap", listOf("\\lam x => suc x"))
        assertEquals("pmap (\\lam x => suc x) {?}", term)
    }

    @Test
    fun `buildTermFromApply fills all prop args as holes`() {
        val gen = makeGenerator()
        val info = SignatureInfoResponse(
            name = "transport",
            params = listOf(
                ParamInfo("A", "\\Type", false, false),
                ParamInfo("B", "A -> \\Type", true, false),
                ParamInfo("a", "A", false, false),
                ParamInfo("a'", "A", false, false),
                ParamInfo("p", "a = a'", true, true),
                ParamInfo("b", "B a", true, false)
            ),
            resultType = "B a'"
        )
        val cacheField = gen.javaClass.getDeclaredField("sigInfoCache")
        cacheField.isAccessible = true
        @Suppress("UNCHECKED_CAST")
        val cache = cacheField.get(gen) as MutableMap<String, SignatureInfoResponse>
        cache["transport"] = info

        val term = gen.buildTermFromApply("transport", listOf("\\lam x => x = 0", "h"))
        assertEquals("transport (\\lam x => x = 0) {?} h", term)
    }

    @Test
    fun `buildTermFromApply returns null for unknown name`() {
        val gen = makeGenerator()
        val term = gen.buildTermFromApply("unknown", emptyList())
        assertNull(term)
    }

    @Test
    fun `parseStepFromResponse handles dotted field access`() {
        val gen = makeGenerator()
        val response = """
            Plan: Apply isIrr on p.
            [APPLY p.isIrr]
            inv k|n.inv-right
            [/APPLY]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("apply", step.type)
        assertEquals("p.isIrr", step.name)
        assertEquals(1, step.args.size)
        assertEquals("inv k|n.inv-right", step.args[0])
    }

    @Test
    fun `buildTermFromApply resolves dotted field access via field sig info`() {
        val gen = makeGenerator()
        val info = SignatureInfoResponse(
            name = "isIrr",
            params = listOf(
                ParamInfo("M", "CMonoid", false, false),
                ParamInfo("e", "M", false, false),
                ParamInfo("this", "Irr e", false, false),
                ParamInfo("x", "M", false, false),
                ParamInfo("y", "M", false, false),
                ParamInfo("p0", "e = x * y", true, true)
            ),
            resultType = "Inv x || Inv y"
        )
        val cacheField = gen.javaClass.getDeclaredField("sigInfoCache")
        cacheField.isAccessible = true
        @Suppress("UNCHECKED_CAST")
        val cache = cacheField.get(gen) as MutableMap<String, SignatureInfoResponse>
        cache["isIrr"] = info

        val term = gen.buildTermFromApply("p.isIrr", listOf("inv k|n.inv-right"))
        assertEquals("p.isIrr {?}", term)
    }

    @Test
    fun `buildTermFromApply passes implicit args before explicit params`() {
        val gen = makeGenerator()
        val info = SignatureInfoResponse(
            name = "isIrr",
            params = listOf(
                ParamInfo("M", "CMonoid", false, false),
                ParamInfo("e", "M", false, false),
                ParamInfo("x", "M", false, false),
                ParamInfo("y", "M", false, false),
                ParamInfo("_", "e = x * y", true, true)
            ),
            resultType = "Inv x || Inv y"
        )
        val cacheField = gen.javaClass.getDeclaredField("sigInfoCache")
        cacheField.isAccessible = true
        @Suppress("UNCHECKED_CAST")
        val cache = cacheField.get(gen) as MutableMap<String, SignatureInfoResponse>
        cache["isIrr"] = info

        val term = gen.buildTermFromApply("p.isIrr", listOf("{k}", "{k|n.inv}"))
        assertEquals("p.isIrr {k} {k|n.inv} {?}", term)
    }

    @Test
    fun `buildTermFromApply mixes implicit and explicit args`() {
        val gen = makeGenerator()
        val info = SignatureInfoResponse(
            name = "pmap",
            params = listOf(
                ParamInfo("A", "\\Type", false, false),
                ParamInfo("B", "\\Type", false, false),
                ParamInfo("a", "A", false, false),
                ParamInfo("a'", "A", false, false),
                ParamInfo("f", "A -> B", true, false),
                ParamInfo("p", "a = a'", true, true)
            ),
            resultType = "f a = f a'"
        )
        val cacheField = gen.javaClass.getDeclaredField("sigInfoCache")
        cacheField.isAccessible = true
        @Suppress("UNCHECKED_CAST")
        val cache = cacheField.get(gen) as MutableMap<String, SignatureInfoResponse>
        cache["pmap"] = info

        val term = gen.buildTermFromApply("pmap", listOf("{Nat}", "\\lam x => suc x"))
        assertEquals("pmap {Nat} (\\lam x => suc x) {?}", term)
    }

    @Test
    fun `buildCaseExpression generates case from variable type`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Nat"] = SignatureInfoResponse(
            name = "Nat",
            params = emptyList(),
            resultType = null,
            constructors = listOf(
                ConstructorInfo("0", emptyList()),
                ConstructorInfo("suc", listOf(ConstructorParam("n", "Nat", true)))
            )
        )
        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D")
        val goal = PlainTextGoal("0", "P n", listOf(ContextBinding("n", "Nat")), "M:D")
        val result = gen.buildCaseExpression("n", "Nat", "")
        assertEquals("\\case \\elim n \\with { | 0 => {?} | suc n => {?} }", result)
    }

    @Test
    fun `buildCaseExpression generates top-level elim for variable`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Nat"] = SignatureInfoResponse(
            name = "Nat",
            params = emptyList(),
            resultType = null,
            constructors = listOf(
                ConstructorInfo("0", emptyList()),
                ConstructorInfo("suc", listOf(ConstructorParam("n", "Nat", true)))
            )
        )
        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D")
        val goal = PlainTextGoal("0", "P n", listOf(ContextBinding("n", "Nat")), "M:D")
        val result = gen.buildCaseExpression("n", "Nat", "", topLevel = true)
        assertEquals("\\elim n | 0 => {?} | suc n => {?}", result)
    }

    @Test
    fun `buildCaseExpression uses case elim for expression even at top level`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Dec"] = SignatureInfoResponse(
            name = "Dec",
            params = listOf(ParamInfo("P", "\\Prop", true, false)),
            resultType = null,
            constructors = listOf(
                ConstructorInfo("yes", listOf(ConstructorParam("p", "P", true))),
                ConstructorInfo("no", listOf(ConstructorParam("q", "Not P", true)))
            )
        )
        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D")
        val goal = PlainTextGoal("0", "x = y", listOf(
            ContextBinding("x", "Nat"), ContextBinding("y", "Nat")
        ), "M:D")
        val result = gen.buildCaseExpression("decideEq x y", "Dec", "", topLevel = true)
        assertEquals("\\case decideEq x y \\with { | yes p => {?} | no q => {?} }", result)
    }

    @Test
    fun `buildCaseExpression returns null for unknown variable`() {
        val cli = FakeCli()
        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D")
        val goal = PlainTextGoal("0", "P x", listOf(ContextBinding("x", "Foo")), "M:D")
        val result = gen.buildCaseExpression("x", "Foo", "")
        assertNull(result)
    }

    @Test
    fun `buildCaseExpression handles expression without elim`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Dec"] = SignatureInfoResponse(
            name = "Dec",
            params = listOf(ParamInfo("P", "\\Prop", true, false)),
            resultType = null,
            constructors = listOf(
                ConstructorInfo("yes", listOf(ConstructorParam("p", "P", true))),
                ConstructorInfo("no", listOf(ConstructorParam("q", "Not P", true)))
            )
        )
        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D")
        val goal = PlainTextGoal("0", "x = y", listOf(
            ContextBinding("x", "Nat"), ContextBinding("y", "Nat")
        ), "M:D")
        val result = gen.buildCaseExpression("decideEq x y", "Dec", "Set")
        assertEquals("\\case decideEq x y \\with { | yes p => {?} | no q => {?} }", result)
    }

    @Test
    fun `parseStepFromResponse picks last tag across types`() {
        val gen = makeGenerator()
        val response = """
            Let me try byLeft first.
            [APPLY byLeft]
            [/APPLY]
            Actually, I should case split on the isIrr result.
            [CASE]p.isIrr (inv k|n.inv-right)[/CASE]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("case", step.type)
        assertEquals("p.isIrr (inv k|n.inv-right)", step.rawTerm)
    }

    @Test
    fun `parseStepFromResponse picks last tag when APPLY is after CASE`() {
        val gen = makeGenerator()
        val response = """
            [CASE]n[/CASE]
            Wait, I should apply pmap instead.
            [APPLY pmap]
            \lam x => suc x
            [/APPLY]
        """.trimIndent()
        val step = gen.parseStepFromResponse(response)
        assertNotNull(step)
        assertEquals("apply", step.type)
        assertEquals("pmap", step.name)
    }

    @Test
    fun `buildTermFromApply fills propositional args as holes`() {
        val gen = makeGenerator()
        val info = SignatureInfoResponse(
            name = "inv",
            params = listOf(
                ParamInfo("A", "\\Type", false, false),
                ParamInfo("a", "A", false, false),
                ParamInfo("a'", "A", false, false),
                ParamInfo("p", "a = a'", true, true)
            ),
            resultType = "a' = a"
        )
        val cacheField = gen.javaClass.getDeclaredField("sigInfoCache")
        cacheField.isAccessible = true
        @Suppress("UNCHECKED_CAST")
        val cache = cacheField.get(gen) as MutableMap<String, SignatureInfoResponse>
        cache["inv"] = info

        val term = gen.buildTermFromApply("inv", listOf("k|n.inv-right"))
        assertEquals("inv {?}", term)
    }

    @Test
    fun `buildIntroExpression with provided names`() {
        val gen = makeGenerator()
        val goal = PlainTextGoal("0", "\\Pi (a : Nat) (b : Nat) -> a = b", emptyList(), "M:D")
        val result = gen.buildIntroExpression(listOf("x", "y"), goal)
        assertEquals("\\lam x y => {?}", result)
    }

    @Test
    fun `buildIntroExpression extracts names from Pi type`() {
        val gen = makeGenerator()
        val goal = PlainTextGoal("0", "\\Pi (n : Nat) (m : Nat) -> n + m = m + n", emptyList(), "M:D")
        val result = gen.buildIntroExpression(emptyList(), goal)
        assertEquals("\\lam n m => {?}", result)
    }

    @Test
    fun `buildIntroExpression extracts names from multi-name Pi binder`() {
        val gen = makeGenerator()
        val goal = PlainTextGoal("0", "\\Pi (a b : Nat) -> a = b", emptyList(), "M:D")
        val result = gen.buildIntroExpression(emptyList(), goal)
        assertEquals("\\lam a b => {?}", result)
    }

    @Test
    fun `buildIntroExpression handles arrow type with underscore`() {
        val gen = makeGenerator()
        val goal = PlainTextGoal("0", "Nat -> Nat", emptyList(), "M:D")
        val result = gen.buildIntroExpression(emptyList(), goal)
        assertEquals("\\lam _ => {?}", result)
    }

    @Test
    fun `buildIntroExpression handles mixed Pi and arrow`() {
        val gen = makeGenerator()
        val goal = PlainTextGoal("0", "\\Pi (n : Nat) -> Nat -> n = n", emptyList(), "M:D")
        val result = gen.buildIntroExpression(emptyList(), goal)
        assertEquals("\\lam n _ => {?}", result)
    }
}

class CaseRecoveryTest {
    @Test
    fun `generate uses a REFINE term verbatim and rejects a bare hole`() {
        val cli = FakeCli()
        cli.applyStepResult = ApplyStepResponse(
            success = true,
            goals = listOf(GoalInfo("0", expectedType = "Nat"), GoalInfo("1", expectedType = "Nat"))
        )

        val llm = ScriptedLLMClient(listOf(
            "[REFINE]{?}[/REFINE]",                          // a lone hole is not a step -> retried
            "[REFINE](mod-lem p {?}, rec-lem p {?})[/REFINE]" // term with holes -> used as-is
        ))

        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D", maxAttempts = 2, maxCandidates = 1, llmClient = llm)
        val goal = PlainTextGoal("0", "\\Sigma Nat Nat", emptyList(), "M:D")
        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(goal))

        val steps = gen.generate(goal, proof)

        assertEquals(1, steps.size)
        assertEquals("((mod-lem p {?}, rec-lem p {?}))", steps[0].proof.toString())
        assertTrue(
            llm.prompts[1].contains("was just {?}"),
            "the retry prompt should explain why a bare hole was rejected, got:\n${llm.prompts[1]}"
        )
    }

    @Test
    fun `generate recovers from failed case attempts and succeeds on valid case`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Nat"] = SignatureInfoResponse(
            name = "Nat",
            constructors = listOf(
                ConstructorInfo("0"),
                ConstructorInfo("suc", listOf(ConstructorParam("n", "Nat", true)))
            )
        )
        // Recovery path 1: typeExpr fails on the first split expression.
        // Recovery path 2: the second expression's type is not a datatype.
        // The third attempt is a proper datatype variable.
        cli.typeExprResponses["decideEq x y"] =
            TypeExprResponse(null, "[ERROR] Cannot resolve reference 'decideEq'")
        cli.typeExprResponses["\\lam x => x"] =
            TypeExprResponse(TypeExprData(type = "Nat -> Nat", datatype = null))
        cli.typeExprResponses["n"] =
            TypeExprResponse(TypeExprData(type = "Nat", datatype = Datatype("Nat", "Prelude")))

        cli.applyStepResult = ApplyStepResponse(
            success = true,
            goals = listOf(
                GoalInfo("0", expectedType = "Nat"),
                GoalInfo("1", expectedType = "Nat")
            )
        )

        val llm = ScriptedLLMClient(listOf(
            "[CASE]decideEq x y[/CASE]",   // typeExpr error -> retried
            "[CASE]\\lam x => x[/CASE]",   // not a datatype -> retried
            "[CASE]n[/CASE]",              // valid -> accepted as candidate #1
            "[CASE]n[/CASE]",              // same as accepted -> duplicate-of-accepted
            "[CASE]n[/CASE]"               // same again -> attempts exhausted
        ))

        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D", maxAttempts = 5, llmClient = llm)
        val goal = PlainTextGoal("0", "Nat", listOf(ContextBinding("n", "Nat")), "M:D")
        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(goal))

        val steps = gen.generate(goal, proof)

        // Both failed CASE attempts were retried, then the valid one went through
        assertEquals(listOf("decideEq x y", "\\lam x => x", "n"), cli.typeExprCalls)
        assertEquals(1, steps.size)
        assertEquals("(\\elim n | 0 => {?} | suc n => {?})", steps[0].proof.toString())

        // The retry feedback carried the actual failure reasons back to the model
        assertTrue(
            llm.prompts[1].contains("Typechecking split expression decideEq x y resulted in error: [ERROR] Cannot resolve reference 'decideEq'"),
            "second prompt should contain the typeExpr error, got:\n${llm.prompts[1]}"
        )
        assertTrue(
            llm.prompts[2].contains("Cannot recognize the type of '\\lam x => x' as a datatype"),
            "third prompt should contain the not-a-datatype feedback, got:\n${llm.prompts[2]}"
        )
        // After a success, the generator asks for a DIFFERENT step and rejects repeats of accepted ones
        assertTrue(
            llm.prompts[3].contains("ACCEPTED as candidate #1"),
            "fourth prompt should announce the accepted candidate, got:\n${llm.prompts[3]}"
        )
        assertTrue(
            llm.prompts[4].contains("it was ACCEPTED as a candidate"),
            "fifth prompt should reject the repeat of an accepted step, got:\n${llm.prompts[4]}"
        )
    }

    @Test
    fun `generate collects multiple distinct candidates`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Nat"] = SignatureInfoResponse(
            name = "Nat",
            constructors = listOf(
                ConstructorInfo("0"),
                ConstructorInfo("suc", listOf(ConstructorParam("n", "Nat", true)))
            )
        )
        cli.typeExprResponses["n"] =
            TypeExprResponse(TypeExprData(type = "Nat", datatype = Datatype("Nat", "Prelude")))
        cli.typeExprResponses["m"] =
            TypeExprResponse(TypeExprData(type = "Nat", datatype = Datatype("Nat", "Prelude")))
        cli.applyStepResult = ApplyStepResponse(
            success = true,
            goals = listOf(GoalInfo("0", expectedType = "Nat"), GoalInfo("1", expectedType = "Nat"))
        )

        val llm = ScriptedLLMClient(listOf(
            "[CASE]n[/CASE]",
            "[CASE]m[/CASE]"
        ))

        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(
            cli, "M:D", maxAttempts = 5, maxCandidates = 2, llmClient = llm
        )
        val goal = PlainTextGoal("0", "Nat", listOf(
            ContextBinding("n", "Nat"), ContextBinding("m", "Nat")
        ), "M:D")
        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(goal))

        val steps = gen.generate(goal, proof)

        assertEquals(2, steps.size)
        assertEquals("(\\elim n | 0 => {?} | suc n => {?})", steps[0].proof.toString())
        assertEquals("(\\elim m | 0 => {?} | suc m => {?})", steps[1].proof.toString())
        assertEquals(2, llm.prompts.size, "stops asking once maxCandidates is reached")
        assertTrue(llm.prompts[1].contains("ACCEPTED as candidate #1"))
        assertTrue(llm.prompts[1].contains("DIFFERENT"))
    }

    @Test
    fun `independent mode runs attempts with fresh prompt and filters duplicates`() {
        val cli = FakeCli()
        cli.signatureInfoResults["Nat"] = SignatureInfoResponse(
            name = "Nat",
            constructors = listOf(
                ConstructorInfo("0"),
                ConstructorInfo("suc", listOf(ConstructorParam("n", "Nat", true)))
            )
        )
        cli.typeExprResponses["n"] =
            TypeExprResponse(TypeExprData(type = "Nat", datatype = Datatype("Nat", "Prelude")))
        cli.typeExprResponses["m"] =
            TypeExprResponse(TypeExprData(type = "Nat", datatype = Datatype("Nat", "Prelude")))
        cli.applyStepResult = ApplyStepResponse(
            success = true,
            goals = listOf(GoalInfo("0", expectedType = "Nat"), GoalInfo("1", expectedType = "Nat"))
        )

        val llm = ScriptedLLMClient(listOf(
            "[CASE]n[/CASE]",   // accepted -> candidate #1
            "[CASE]n[/CASE]",   // same term -> filtered mechanically (no feedback to model)
            "[CASE]m[/CASE]"    // accepted -> candidate #2
        ))

        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(
            cli, "M:D", maxAttempts = 5, maxCandidates = 2, seekAlternatives = false, llmClient = llm
        )
        val goal = PlainTextGoal("0", "Nat", listOf(
            ContextBinding("n", "Nat"), ContextBinding("m", "Nat")
        ), "M:D")
        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(goal))

        val steps = gen.generate(goal, proof)

        assertEquals(2, steps.size)
        assertEquals("(\\elim n | 0 => {?} | suc n => {?})", steps[0].proof.toString())
        assertEquals("(\\elim m | 0 => {?} | suc m => {?})", steps[1].proof.toString())

        // History erasure: every attempt sees the exact same prompt — the model is
        // NOT told about previous successes and NOT asked for a different attempt.
        assertEquals(3, llm.prompts.size)
        assertTrue(llm.prompts.all { it == llm.prompts[0] }, "independent attempts must share one fresh prompt")
        assertTrue(!llm.prompts[0].contains("ACCEPTED"))
        assertTrue(!llm.prompts[0].contains("DIFFERENT"))
    }

    @Test
    fun `generate does not retry a case step when typeExpr returns null`() {
        // Null means the CLI layer itself is broken (transport failure) — the
        // generator gives up on the goal rather than burning LLM attempts.
        val cli = FakeCli() // typeExprResponses empty -> typeExpr returns null
        val llm = ScriptedLLMClient(listOf("[CASE]n[/CASE]"))
        val gen = typechecker.cli.proofstep.CliLLMStepGenerator(cli, "M:D", maxAttempts = 5, llmClient = llm)
        val goal = PlainTextGoal("0", "Nat", listOf(ContextBinding("n", "Nat")), "M:D")
        val proof = PlainTextProof(cli, "M:D", "{?}", listOf(goal))

        val steps = gen.generate(goal, proof)

        assertTrue(steps.isEmpty())
        assertEquals(1, llm.prompts.size, "should not retry after a null typeExpr response")
    }
}

