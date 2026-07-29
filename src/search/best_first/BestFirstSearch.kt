package search.best_first

import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import java.util.PriorityQueue

class BestFirstSearch<G : Goal<G>>(private val proofStepGenerator: ProofStepGenerator<G>) {
  companion object {
    const val MAX_DEPTH = 10
    /** How many times a goal that yielded no steps is retried when the search gets stuck. */
    const val MAX_GOAL_RETRIES = 2
  }

  /** A node whose expansion stopped because [goal] yielded no proof steps. */
  private data class DeadEnd<G : Goal<G>>(val node: BFSNode<G>, val goal: G)

  // Memoized step generation, keyed by goal AND the proof state it was generated
  // in. A ProofStep embeds the full proof text of the state it was produced from,
  // so reusing it for a different parent state would silently discard that
  // parent's progress on the other goals ("teleport" to the first parent's
  // lineage instead of advancing the current one). Cross-state reuse happens one
  // level down instead: the generator memoizes goal-relative step TERMS and
  // re-validates them against each new state without calling the LLM.
  val generatedSteps : MutableMap<Pair<G, String>, List<ProofStep<G>>> = HashMap()

  fun search(initialProof: Proof<G>): Proof<G>? {
    val nodesQueue = PriorityQueue<BFSNode<G>>(compareBy { it.score })
    // Dead ends, best score first. When the live frontier runs out, these are
    // resurrected one at a time and their failed goal gets a fresh generation
    // round (a sampling model may find steps it missed the first time).
    val deadNodes = PriorityQueue<DeadEnd<G>>(compareBy { it.node.score })
    val retryCounts = mutableMapOf<Pair<G, String>, Int>()
    // DAG search: each distinct proof state is expanded at most once. The same
    // state is reachable via different goal-expansion orders (fill goal A then B,
    // or B then A); without a visited set, every copy is re-queued and its whole
    // subtree re-explored.
    val seenStates = mutableSetOf(initialProof.toString())

    nodesQueue.add(BFSNode(initialProof, 0.0, 0))
    while (true) {
      val node = nodesQueue.poll()
      if (node == null) {
        // Live frontier exhausted — the search is stuck. Resurrect the best dead
        // end for another round, unless its goal already used up its retries.
        val dead = deadNodes.poll() ?: return null
        val retryKey = dead.goal to dead.node.getProof().toString()
        val retries = retryCounts.getOrDefault(retryKey, 0)
        if (retries >= MAX_GOAL_RETRIES) {
          println("Giving up on goal after $retries retries: ${dead.goal}")
          continue
        }
        retryCounts[retryKey] = retries + 1
        generatedSteps.remove(retryKey)
        proofStepGenerator.onRetryGoal(dead.goal)
        println("Search stuck — retrying dead goal (round ${retries + 1}/$MAX_GOAL_RETRIES): ${dead.goal}")
        nodesQueue.add(dead.node)
        continue
      }
      if (node.depth > MAX_DEPTH) { continue }
      for (currentGoal in node.getProof().goals()) {
        val stepsKey = currentGoal to node.getProof().toString()
        var proofSteps = generatedSteps[stepsKey]
        if (proofSteps == null) {
          proofSteps = proofStepGenerator.generate(currentGoal, node.getProof())
          generatedSteps[stepsKey] = proofSteps
        }
        if (proofSteps.isEmpty()) {
          // Dead end: save it (best-first) instead of abandoning — if the search
          // gets stuck elsewhere, this node is retried with a fresh LLM round.
          println("No proof steps found for goal $currentGoal — saved as dead end")
          println("Current proof: ${node.getProof()}")
          deadNodes.add(DeadEnd(node, currentGoal))
          break
        }
        for (proofStep in proofSteps) {
          val expansion = node.applyProofStep(currentGoal, proofStep)
          // Loop check (subsumption): a subgoal identical (same type and context)
          // to a goal already expanded on this branch would re-explore the same
          // possibilities forever — A -> B -> A cycles (inv-involution towers,
          // pmap identity, *> ping-pong). Same type+context means same
          // provability, so the step is sound to reject.
          val repeated = expansion.getProof().goals().find { it in expansion.pathGoals }
          if (repeated != null) {
            println("Skipping step — subgoal already expanded on this branch (regress): $repeated")
            continue
          }
          if (!seenStates.add(expansion.getProof().toString())) {
            println("Skipping already-visited proof state")
            continue
          }
          println("Current proof: ${expansion.getProof()}")
          if (expansion.getProof().isFinished()) {
            return expansion.getProof()
          }
          nodesQueue.add(expansion)
        }
      }
    }
  }
}
