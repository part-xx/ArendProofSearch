package typechecker

open class Goal: Proof {
    final override fun goals(): List<Goal> { return listOf(this) }
    final override fun replaceGoal(goal: Goal, proof: Proof): Proof { return proof }
    // final override fun applyProofStep(goal: Goal, step: ProofStep): Proof { return step.toProof() }
}