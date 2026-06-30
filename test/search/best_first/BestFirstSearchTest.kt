package search.best_first

import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class MockGoal(val name: String) : Goal<MockGoal>() {
    override fun toString() = "MockGoal($name)"
    override fun equals(other: Any?) = other is MockGoal && name == other.name
    override fun hashCode() = name.hashCode()
}

class MockProof(
    private val goalList: List<MockGoal>,
    val label: String = ""
) : Proof<MockGoal> {
    override fun goals() = goalList
    override fun replaceGoal(goal: MockGoal, proof: Proof<MockGoal>): Proof<MockGoal>? {
        if (goal !in goalList) return null
        val remaining = goalList.filter { it != goal } + proof.goals()
        return MockProof(remaining, "$label+${(proof as? MockProof)?.label ?: "?"}")
    }
    override fun toString() = "MockProof($label, goals=${goalList.map { it.name }})"
}

class BestFirstSearchTest {

    @Test
    fun `search returns null when no steps are generated`() {
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                return emptyList()
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val initialProof = MockProof(listOf(MockGoal("g1")))

        val result = search.search(initialProof)
        assertNull(result)
    }

    @Test
    fun `search finds proof when single goal is immediately solved`() {
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                return listOf(ProofStep(MockProof(emptyList(), "solved"), 1.0))
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val initialProof = MockProof(listOf(MockGoal("g1")))

        val result = search.search(initialProof)
        assertNotNull(result)
        assertTrue(result.isFinished())
    }

    @Test
    fun `search handles multi-step proofs`() {
        var callCount = 0
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                callCount++
                return when (goal.name) {
                    "g1" -> listOf(ProofStep(MockProof(listOf(MockGoal("g2")), "step1"), 1.0))
                    "g2" -> listOf(ProofStep(MockProof(emptyList(), "step2"), 1.0))
                    else -> emptyList()
                }
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val initialProof = MockProof(listOf(MockGoal("g1")))

        val result = search.search(initialProof)
        assertNotNull(result)
        assertTrue(result.isFinished())
        assertTrue(callCount >= 2)
    }

    @Test
    fun `search respects MAX_DEPTH limit`() {
        val generator = object : ProofStepGenerator<MockGoal> {
            var depth = 0
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                depth++
                return listOf(ProofStep(MockProof(listOf(MockGoal("g$depth")), "d$depth"), 1.0))
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val initialProof = MockProof(listOf(MockGoal("g0")))

        val result = search.search(initialProof)
        assertNull(result)
    }

    @Test
    fun `search picks lowest score node first`() {
        val expansionOrder = mutableListOf<String>()
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                expansionOrder.add(goal.name)
                return when (goal.name) {
                    "root" -> listOf(
                        ProofStep(MockProof(listOf(MockGoal("high")), "h"), 10.0),
                        ProofStep(MockProof(listOf(MockGoal("low")), "l"), 1.0)
                    )
                    "low" -> listOf(ProofStep(MockProof(emptyList(), "done"), 1.0))
                    "high" -> listOf(ProofStep(MockProof(emptyList(), "done"), 1.0))
                    else -> emptyList()
                }
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val initialProof = MockProof(listOf(MockGoal("root")))

        val result = search.search(initialProof)
        assertNotNull(result)
        assertEquals("root", expansionOrder[0])
        assertEquals("low", expansionOrder[1])
    }

    @Test
    fun `search handles multiple goals in a single proof`() {
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                return listOf(ProofStep(MockProof(emptyList(), "solved_${goal.name}"), 1.0))
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val initialProof = MockProof(listOf(MockGoal("g1"), MockGoal("g2")))

        val result = search.search(initialProof)
        assertNotNull(result)
        assertTrue(result.isFinished())
    }

    @Test
    fun `search handles replaceGoal returning null`() {
        val failingProof = object : Proof<MockGoal> {
            override fun goals() = listOf(MockGoal("g1"))
            override fun replaceGoal(goal: MockGoal, proof: Proof<MockGoal>): Proof<MockGoal>? = null
        }
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                return listOf(ProofStep(MockProof(emptyList(), "step"), 1.0))
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)

        val result = search.search(failingProof)
        assertNull(result)
    }

    @Test
    fun `already finished proof returns immediately`() {
        val generator = object : ProofStepGenerator<MockGoal> {
            override fun generate(goal: MockGoal, currentProof: Proof<MockGoal>?): List<ProofStep<MockGoal>> {
                throw AssertionError("Should not be called for finished proof")
            }
        }
        val search = BestFirstSearch<MockGoal>(generator)
        val finishedProof = MockProof(emptyList(), "done")

        val result = search.search(finishedProof)
        assertNull(result, "BFS only returns from expansion, not from initial state")
    }
}
