package search.best_first

import org.arend.term.concrete.Concrete
import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.impl.ArendProof
import typechecker.impl.proofstep.LLMStepGenerator
import java.util.PriorityQueue

class BestFirstSearch(private val proofStepGenerator: ProofStepGenerator) {
  companion object {
    const val MAX_DEPTH = 5
  }

  fun search(goal: Goal): Proof? {
    val nodesQueue = PriorityQueue<BFSNode>(compareBy { it.score })

    nodesQueue.add(BFSNode(goal, 0.0, 0))
    while (nodesQueue.isNotEmpty()) {
      val node = nodesQueue.poll()
      if (node.depth > MAX_DEPTH) { continue }
      for (goal in node.getProof().goals()) {
        val proofSteps = proofStepGenerator.generate(goal)
        for (proofStep in proofSteps) {
          val expansion = node.applyProofStep(goal, proofStep) ?: continue
          if (proofStepGenerator is LLMStepGenerator) {
            proofStepGenerator.setCurrentProof((expansion.getProof() as ArendProof).getProof()!!)
          }
          println("Current proof: ${expansion.getProof()}")
          readln()
          if (expansion.getProof().isFinished()) {
            return expansion.getProof()
          }
          nodesQueue.add(expansion)
        }
      }
    }
    return null
  }
}