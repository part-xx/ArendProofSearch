package typechecker

interface Proof {
    fun goals(): List<Goal>
    fun replaceGoal(goal: Goal, proof: Proof): Proof?
    // fun applyProofStep(goal: Goal, step: ProofStep): Proof?

    fun isFinished(): Boolean = goals().isEmpty()
}