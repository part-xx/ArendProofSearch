package search.best_first

import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStepGenerator
import java.util.PriorityQueue

class BestFirstSearch<G : Goal<G>>(private val proofStepGenerator: ProofStepGenerator<G>) {
  companion object {
    const val MAX_DEPTH = 5
  }

  fun search(initialProof: Proof<G>): Proof<G>? {
    val nodesQueue = PriorityQueue<BFSNode<G>>(compareBy { it.score })

    nodesQueue.add(BFSNode(initialProof, 0.0, 0))
    while (nodesQueue.isNotEmpty()) {
      val node = nodesQueue.poll()
      if (node.depth > MAX_DEPTH) { continue }
      for (currentGoal in node.getProof().goals()) {
        val proofSteps = proofStepGenerator.generate(currentGoal, node.getProof())
        if (proofSteps.isEmpty()) {
          println("No proof steps found for goal $currentGoal")
          println("Current proof: ${node.getProof()}")
          return null
        }
        for (proofStep in proofSteps) {
          val expansion = node.applyProofStep(currentGoal, proofStep)
          println("Current proof: ${expansion.getProof()}")
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
