package search.best_first

import search.Node
import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep

class BFSNode<G : Goal<G>>(
    private val _proof: Proof<G>,
    val score: Double,
    val depth: Int,
    /** Goals expanded along the path from the root to this node — the subsumption
     *  set for the loop check: a new subgoal identical to one of these re-explores
     *  an ancestor's possibilities (same type+context means same provability). */
    val pathGoals: Set<G> = emptySet()
): Node<G> {
    override fun getProof(): Proof<G> {
        return _proof
    }

    override fun applyProofStep(goal: G, proofStep: ProofStep<G>): BFSNode<G> {
        return BFSNode(proofStep.proof, score + proofStep.score, depth + 1, pathGoals + goal)
    }
}
