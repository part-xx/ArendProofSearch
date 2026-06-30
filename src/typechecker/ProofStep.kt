package typechecker

data class ProofStep<G : Goal<G>>(val proof: Proof<G>, val score: Double)

interface ProofStepGenerator<G : Goal<G>> {
    fun generate(goal: G, currentProof: Proof<G>? = null): List<ProofStep<G>>
}
