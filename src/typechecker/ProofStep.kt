package typechecker

data class ProofStep<G : Goal<G>>(val proof: Proof<G>, val score: Double)

interface ProofStepGenerator<G : Goal<G>> {
    fun generate(goal: G, currentProof: Proof<G>? = null): List<ProofStep<G>>

    /**
     * Called when the search resurrects a goal that previously yielded no steps
     * and retries it with a fresh generation round. Implementations that memoize
     * negative results should invalidate them for [goal] here, so the next
     * [generate] call actually retries instead of short-circuiting.
     */
    fun onRetryGoal(goal: G) {}
}
