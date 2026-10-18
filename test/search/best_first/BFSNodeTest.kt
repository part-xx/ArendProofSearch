package search.best_first

import typechecker.ProofStep
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
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
    fun `applyProofStep takes the step's proof as the whole new state`() {
        // A step carries the full proof state it leads to; the generator has already composed it
        val node = BFSNode(MockProof(listOf(MockGoal("g1"), MockGoal("g2")), "initial"), 0.0, 0)
        val composed = MockProof(listOf(MockGoal("g2"), MockGoal("g3")), "initial+step")

        val result = node.applyProofStep(MockGoal("g1"), ProofStep(composed, 1.0))
        assertEquals(composed, result.getProof())
        assertEquals(listOf("g2", "g3"), result.getProof().goals().map { it.name })
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
    fun `applyProofStep records the expanded goal on the path`() {
        val node = BFSNode(MockProof(listOf(MockGoal("g1")), "initial"), 0.0, 0, pathGoals = setOf(MockGoal("g0")))

        val result = node.applyProofStep(MockGoal("g1"), ProofStep(MockProof(emptyList(), "solved"), 1.0))
        assertEquals(setOf(MockGoal("g0"), MockGoal("g1")), result.pathGoals)
    }
}
