package typechecker.coreapi.proofstep

import typechecker.coreapi.ArendGoal

/**
 * Retrieves library lemmas to split on with `\case L x... \with { ... }`, as arend-lib proofs do with
 * `\case totality x y` (`meet-isMin`), `\case FinSum_char x` (`FinSum_zro`, `FinSum-unique`,
 * `FinSum-pred`) or `\case Big01_meet-isMin l a` (`Big_meet-isMin`): the definitions concluding a
 * disjunction, a decision or a truncated existence ([CASE_HEADS]) among those the CLI's proof search
 * finds for a function symbol of the goal. Those mentioning it in their conclusion, as `FinSum_char`
 * does `FinSum`, come first. Which variables of the context they are applied to is decided by
 * [CaseGenerator].
 */
class SplitRetriever(private val index: SignatureIndex, private val maxCandidates: Int = 40, private val maxSymbols: Int = 3) : PremiseRetriever {
  companion object {
    /** The heads of the types a proof splits on; `∃` is how a truncated `\Sigma` prints. */
    val CASE_HEADS = listOf("TruncP", "||", "Dec", "∃")
    /** The symbol of the goal occurs in the lemma's conclusion. */
    const val CONCLUSION_COST = 1.3
    /** The symbol of the goal occurs only in the lemma's parameters. */
    const val PARAMETER_COST = 1.6

    /** Whether a lemma with the codomain [codomain] (as tokens) is one to split on. */
    fun isSplittable(codomain: List<String>): Boolean = codomain.firstOrNull() in CASE_HEADS || "||" in codomain
  }

  /** The lemmas to split on found for each symbol: the same symbols recur in every subgoal. */
  private val bySymbol = HashMap<Symbol, List<PremiseCandidate>>()

  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> {
    val candidates = LinkedHashMap<Pair<String?, String>, PremiseCandidate>()
    for (symbol in symbols(goal)) {
      for (candidate in bySymbol.getOrPut(symbol) { forSymbol(symbol) }) {
        val key = candidate.module to candidate.name
        if (candidates[key]?.let { it.cost <= candidate.cost } != true) candidates[key] = candidate
      }
    }
    return candidates.values.sortedBy { it.cost }.take(maxCandidates)
  }

  private fun forSymbol(symbol: Symbol): List<PremiseCandidate> = index.bySymbol(symbol).mapNotNull { entry ->
    if (!isSplittable(entry.codomain)) return@mapNotNull null
    PremiseCandidate(entry.name, entry.module, if (symbol.occursIn(entry.codomain.joinToString(" "))) CONCLUSION_COST else PARAMETER_COST)
  }

  /** The symbols of the goal that are searched for, outermost first: those of the [BenchmarkTest] indexing phase too. */
  fun symbols(goal: ArendGoal): List<Symbol> = EquationRetriever.functionSymbols(goal.expectedType).take(maxSymbols)
}
