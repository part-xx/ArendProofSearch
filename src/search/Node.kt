package search

import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep

interface Node {
    fun getProof(): Proof
    fun applyProofStep(goal: Goal, proofStep: ProofStep): Node?
}