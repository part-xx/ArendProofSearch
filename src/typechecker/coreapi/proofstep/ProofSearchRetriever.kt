package typechecker.coreapi.proofstep

import typechecker.cli.CliApi
import typechecker.coreapi.ArendGoal

/**
 * Retrieves premises with the Arend CLI's proof search (`-ps`), which matches definitions by the
 * shape of their signature rather than by name.
 *
 * For a goal whose type has head `H`, it takes the definitions whose codomain mentions `H` from the
 * [SignatureIndex]; those that also mention another function `f` of the goal, or take a parameter
 * headed like a hypothesis of the context, are ranked first.
 */
class ProofSearchRetriever(private val index: SignatureIndex, private val maxCandidates: Int = 5000, private val maxSymbols: Int = 3) : PremiseRetriever {
  constructor(cli: CliApi, maxCandidates: Int = 5000, maxSymbols: Int = 3) : this(SignatureIndex(cli), maxCandidates, maxSymbols)

  companion object {
    /** Concludes the goal's head directly: `H ...`. */
    const val HEAD_COST = 1.0
    /** Mentions the goal's head at the top of the codomain, e.g. as an infix operator. */
    const val TOP_LEVEL_COST = 1.5
    /** Mentions the goal's head somewhere inside the codomain. */
    const val NESTED_COST = 2.0
    /** Subtracted for definitions that take one of the goal's hypotheses. */
    const val HYPOTHESIS_BONUS = 0.2
    /** Subtracted for definitions whose codomain also mentions another function of the goal. */
    const val SPECIFIC_BONUS = 0.25
    /** A lemma concluding `P (f x)` for a parameter `P`, retrieved for a goal headed by a variable. */
    const val VARIABLE_HEAD_COST = 1.2
    /** Added for definitions whose parameters mention the head too (`cancel-left : x + y = x + z -> y = z`): among equal conclusions, direct ones first. */
    const val PARAMETER_PENALTY = 0.15

    /** Splits [expression] at the spaces outside of parentheses and braces. */
    fun topLevelTokens(expression: String): List<String> {
      val tokens = mutableListOf<String>()
      val current = StringBuilder()
      var depth = 0
      for (c in expression) {
        when (c) {
          '(', '{', '[' -> depth++
          ')', '}', ']' -> depth--
        }
        if (c == ' ' && depth == 0) {
          if (current.isNotEmpty()) tokens.add(current.toString())
          current.clear()
        } else {
          current.append(c)
        }
      }
      if (current.isNotEmpty()) tokens.add(current.toString())
      return tokens
    }

    /** The cost of a match whose codomain is [codomain], or null if [head] does not occur in it. */
    fun codomainCost(codomain: List<String>, head: Symbol): Double? = when {
      // `H ...`, or an infix `a H b` such as `n < m`. Ranking every top-level `<=` (as in `x <= y ∧ z`)
      // as a head was tried: it fills the premises with unrelated `<=` lemmas
      codomain.firstOrNull()?.let(head::matches) == true -> HEAD_COST
      codomain.size == 3 && head.matches(codomain[1]) -> HEAD_COST
      codomain.any(head::matches) -> TOP_LEVEL_COST
      codomain.any(head::occursIn) -> NESTED_COST
      else -> null
    }

    fun codomainCost(codomain: List<String>, head: String): Double? = codomainCost(codomain, Symbol(head))

    /** The tokens of the codomain of a printed slice `p1 -> ... -> codomain`. */
    fun codomainTokens(expression: String): List<String> {
      val tokens = topLevelTokens(expression)
      return tokens.subList(tokens.lastIndexOf("->") + 1, tokens.size)
    }
  }

  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> {
    val head = PremiseRetriever.head(goal.expectedType) ?: return retrieveForVariableHead(goal)
    // Definitions also mentioning another function of the goal (`meet` for `x ∧ y <= x`) are the specific ones
    val otherSymbols = EquationRetriever.functionSymbols(goal.expectedType).filter { it != head }.take(maxSymbols)
    val hypothesisHeads = goal.typechecker.context.values.mapNotNull { PremiseRetriever.head(it.type) }.distinct()
    val candidates = index.bySymbol(head).mapNotNull { entry ->
      val cost = codomainCost(entry.codomain, head) ?: return@mapNotNull null
      val specific = if (otherSymbols.any { it.occursIn(entry.text) }) SPECIFIC_BONUS else 0.0
      val hypothesis = if (hypothesisHeads.any { it.occursIn(entry.parameters) }) HYPOTHESIS_BONUS else 0.0
      val parameter = if (head.occursIn(entry.parameters)) PARAMETER_PENALTY else 0.0
      PremiseCandidate(entry.name, entry.module, cost - specific - hypothesis + parameter)
    }
    return candidates
      .groupBy { it.module to it.name }
      .map { (_, sameDefinition) -> sameDefinition.minBy { it.cost } }
      .sortedBy { it.cost }
      .take(maxCandidates)
  }

  /**
   * A goal headed by a variable, `P (BigSum l)` for a predicate `P` of the context (`BigSum-pred`,
   * `FinSum-pred`), is searched by the functions it applies: the lemmas concluding something about
   * them for any predicate, `BigSum-pred : P (BigSum l)`, mention them in their codomain.
   */
  private fun retrieveForVariableHead(goal: ArendGoal): List<PremiseCandidate> {
    val symbols = EquationRetriever.functionSymbols(goal.expectedType).take(maxSymbols)
    return symbols.flatMap { symbol ->
      index.bySymbol(symbol).mapNotNull { entry ->
        val codomain = entry.codomain.joinToString(" ")
        // The conclusion is an application of a parameter to something about the symbol: `P (BigSum l)`, not `BigSum l = x`
        if (!symbol.occursIn(codomain) || entry.codomain.firstOrNull()?.let { it.isEmpty() || !it[0].isLetter() || symbol.matches(it) } != false) return@mapNotNull null
        PremiseCandidate(entry.name, entry.module, VARIABLE_HEAD_COST)
      }
    }.distinctBy { it.module to it.name }.take(maxCandidates)
  }
}
