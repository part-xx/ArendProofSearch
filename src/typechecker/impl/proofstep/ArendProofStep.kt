package typechecker.impl.proofstep

import typechecker.Proof
import typechecker.ProofStep
import typechecker.impl.ArendProof

class ArendProofStep(private val proof: ArendProof, score: Double) : ProofStep(score)  {
  override fun toProof(): Proof {
    return proof
  }
}