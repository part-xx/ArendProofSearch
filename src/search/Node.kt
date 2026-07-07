package search

import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep

interface Node<G : Goal<G>> {
    fun getProof(): Proof<G>
    fun applyProofStep(goal: G, proofStep: ProofStep<G>): Node<G>
}
