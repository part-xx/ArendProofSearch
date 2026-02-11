package typechecker

abstract class ProofStep(val score: Double) {
    abstract fun toProof(): Proof
}

interface ProofStepGenerator {
    fun generate(goal: Goal): List<ProofStep>
}