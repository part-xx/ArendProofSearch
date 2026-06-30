package search.best_first

import typechecker.Proof
import typechecker.ProofStep
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BFSNodeTest {

    @Test
    fun `getProof returns the proof passed to constructor`() {
        val proof = MockProof(listOf(MockGoal("g1")), "test")
        val node = BFSNode(proof, 0.0, 0)
        assertEquals(proof, node.getProof())
    }

    @Test
    fun `applyProofStep returns new node with accumulated score`() {
        val proof = MockProof(listOf(MockGoal("g1")), "initial")
        val node = BFSNode(proof, 2.0, 1)

        val stepProof = MockProof(emptyList(), "solved")
        val step = ProofStep(stepProof, 3.0)

        val result = node.applyProofStep(MockGoal("g1"), step)
        assertNotNull(result)
        assertEquals(5.0, result.score)
        assertEquals(2, result.depth)
    }

    @Test
    fun `applyProofStep returns null when replaceGoal fails`() {
        val failingProof = object : Proof<MockGoal> {
            override fun goals() = listOf(MockGoal("g1"))
            override fun replaceGoal(goal: MockGoal, proof: Proof<MockGoal>): Proof<MockGoal>? = null
        }
        val node = BFSNode(failingProof, 0.0, 0)

        val step = ProofStep(MockProof(emptyList(), "solved"), 1.0)
        val result = node.applyProofStep(MockGoal("g1"), step)
        assertNull(result)
    }

    @Test
    fun `applyProofStep increments depth`() {
        val proof = MockProof(listOf(MockGoal("g1")), "initial")
        val node = BFSNode(proof, 0.0, 3)

        val stepProof = MockProof(emptyList(), "solved")
        val step = ProofStep(stepProof, 1.0)

        val result = node.applyProofStep(MockGoal("g1"), step)
        assertNotNull(result)
        assertEquals(4, result.depth)
    }

    @Test
    fun `resulting proof reflects goal replacement`() {
        val proof = MockProof(listOf(MockGoal("g1"), MockGoal("g2")), "initial")
        val node = BFSNode(proof, 0.0, 0)

        val stepProof = MockProof(emptyList(), "solved_g1")
        val step = ProofStep(stepProof, 1.0)

        val result = node.applyProofStep(MockGoal("g1"), step)
        assertNotNull(result)
        val remaining = result.getProof().goals()
        assertEquals(1, remaining.size)
        assertEquals("g2", remaining[0].name)
    }
}
