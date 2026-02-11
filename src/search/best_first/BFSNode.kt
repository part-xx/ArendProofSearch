package search.best_first

import search.Node
import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep

class BFSNode(private val _proof: Proof, val score: Double, val depth: Int): Node {
    override fun getProof(): Proof {
        return _proof
    }

    override fun applyProofStep(goal: Goal, proofStep: ProofStep): BFSNode? {
        val newProof = _proof.replaceGoal(goal, proofStep.toProof()) ?: return null
        return BFSNode(newProof, score + proofStep.score, depth + 1)
    }
}