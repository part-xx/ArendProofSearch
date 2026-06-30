package typechecker

interface Proof<G : Goal<G>> {
    fun goals(): List<G>
    fun replaceGoal(goal: G, proof: Proof<G>): Proof<G>?
    fun isFinished(): Boolean = goals().isEmpty()
}
