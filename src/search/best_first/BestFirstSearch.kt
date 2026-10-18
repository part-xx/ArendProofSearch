package search.best_first

import typechecker.Goal
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import java.util.PriorityQueue

class BestFirstSearch<G : Goal<G>>(
  private val proofStepGenerator: ProofStepGenerator<G>,
  /** The search gives up after expanding this many proof states. */
  private val maxExpansions: Int = Int.MAX_VALUE,
  /**
   * Expand only the first open goal of each proof state. Every goal has to be filled eventually,
   * so no proof is lost, while expanding all goals explores the alternatives of independent
   * branches in every combination.
   */
  private val focusFirstGoal: Boolean = false,
  /**
   * Added to a state's priority for each of its open goals, as an estimate of the cost still
   * ahead: states that close their goals are preferred over ones that only open new branches.
   */
  private val openGoalCost: Double = 0.0,
  /** The most steps a proof may take; every step counts, including those that close a goal. */
  private val maxDepth: Int = MAX_DEPTH,
  /** The search gives up after this many milliseconds. */
  private val maxMillis: Long = Long.MAX_VALUE
) {
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

  fun search(initialProof: Proof<G>): Proof<G>? =

    // The deadline is the step generator's state too: a later search, or a test in the same JVM, must not inherit it

    try { searchUnderDeadline(initialProof) } finally { proofStepGenerator.setDeadline(Long.MAX_VALUE) }


  private fun searchUnderDeadline(initialProof: Proof<G>): Proof<G>? {
    // Ties break by insertion order, so that a search is repeatable
    var inserted = 0L
    val nodesQueue = PriorityQueue<Pair<BFSNode<G>, Long>>(compareBy({ it.first.score + openGoalCost * it.first.getProof().goals().size }, { it.second }))
    fun enqueue(node: BFSNode<G>) { nodesQueue.add(node to inserted++) }
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
    // Two proof texts with the same open goals (same statements over the same contexts) are the same problem: a split
    // on `n` then `l` leaves what a split on `l` then `n` leaves. The first expanded is the cheapest, so later ones are dropped.
    val expandedProblems = HashSet<String>()

    enqueue(BFSNode(initialProof, 0.0, 0))
    var expansions = 0
    val deadline = if (maxMillis == Long.MAX_VALUE) Long.MAX_VALUE else System.currentTimeMillis() + maxMillis
    proofStepGenerator.setDeadline(deadline)
    while (true) {
      if (System.currentTimeMillis() > deadline) {
        println("Giving up after ${maxMillis}ms")
        return null
      }
      val node = nodesQueue.poll()?.first
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
        expandedProblems.remove(dead.node.getProof().goals().map { it.toString() }.sorted().joinToString("\n"))
        proofStepGenerator.onRetryGoal(dead.goal)
        println("Search stuck — retrying dead goal (round ${retries + 1}/$MAX_GOAL_RETRIES): ${dead.goal}")
        enqueue(dead.node)
        continue
      }
      if (node.depth > maxDepth) { continue }
      if (++expansions > maxExpansions) {
        println("Giving up after $maxExpansions expansions")
        return null
      }
      val goals = node.getProof().goals()
      if (!expandedProblems.add(goals.map { it.toString() }.sorted().joinToString("\n"))) {
        println("Skipping state whose open goals were already expanded: ${node.getProof()} -- ${goals.joinToString(" | ")}")
        expansions--
        continue
      }
      println("Expanding #$expansions (score ${"%.2f".format(node.score)}, ${goals.size} open): ${node.getProof()}")
      for (currentGoal in if (focusFirstGoal) goals.take(1) else goals) {
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
          // By identity: the same problem may legitimately come up twice in one proof, as `P` in `r-con p-con (q-con p-con)`
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
          enqueue(expansion)
        }
      }
    }
  }
}
