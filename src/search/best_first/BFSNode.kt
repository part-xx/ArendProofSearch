package search.best_first

import search.Node
import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep

class BFSNode<G : Goal<G>>(private val _proof: Proof<G>, val score: Double, val depth: Int): Node<G> {
    override fun getProof(): Proof<G> {
        return _proof
    }

    override fun applyProofStep(goal: G, proofStep: ProofStep<G>): BFSNode<G>? {
        val newProof = _proof.replaceGoal(goal, proofStep.proof) ?: return null
        return BFSNode(newProof, score + proofStep.score, depth + 1)
    }
}
