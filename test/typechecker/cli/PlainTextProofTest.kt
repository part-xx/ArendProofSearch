package typechecker.cli

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class FakeCli : CliApi {
    var findGoalsResult: FindGoalsResponse = FindGoalsResponse("M:D", emptyList())
    var applyStepResult: ApplyStepResponse = ApplyStepResponse(false)
    var checkExpressionResult: CheckResult = CheckResult(false)
    var scopeResult: ScopeResponse = ScopeResponse()
    var proofSearchResult: ProofSearchResponse = ProofSearchResponse()

    val findGoalsCalls = mutableListOf<String>()
    val applyStepCalls = mutableListOf<Triple<String, String, String>>()

    override fun findGoals(moduleDef: String): FindGoalsResponse {
        findGoalsCalls.add(moduleDef)
        return findGoalsResult
    }

    override fun checkExpression(moduleDef: String, goalId: String, expression: String): CheckResult {
        return checkExpressionResult
    }

    override fun applyStep(moduleDef: String, goalId: String, expression: String): ApplyStepResponse {
        applyStepCalls.add(Triple(moduleDef, goalId, expression))
        return applyStepResult
    }

    override fun getScope(moduleDef: String, goalId: String): ScopeResponse {
        return scopeResult
    }

    override fun proofSearch(pattern: String): ProofSearchResponse {
        return proofSearchResult
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
            listOf(PlainTextGoal("2", "Nat", emptyList(), "TestMod:lemma1")))
        val goal = proof.goals()[0]
        val replacement = PlainTextProof(cli, "TestMod:lemma1", "idp")

        proof.replaceGoal(goal, replacement)

        assertEquals(1, cli.applyStepCalls.size)
        assertEquals("TestMod:lemma1", cli.applyStepCalls[0].first)
        assertEquals("2", cli.applyStepCalls[0].second)
        assertEquals("idp", cli.applyStepCalls[0].third)
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
