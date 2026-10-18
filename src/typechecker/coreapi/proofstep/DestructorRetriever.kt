package typechecker.coreapi.proofstep

import org.arend.core.expr.Expression
import typechecker.coreapi.ArendGoal

/**
 * Retrieves the functions a hypothesis `p : f a = f b` can be mapped over to conclude `a = b`:
 * `pmap pred p` (`id/=suc`, `fin_nat-inj`), `pmap iabs p` (`unpos`), `pmap (fpred x) p` (`unfsuc`).
 * They are the `\func`s found for the type of the hypothesis's sides whose last explicit parameter
 * has that type and whose result has the type of the goal's sides; the typechecker then decides
 * whether `g (f a)` computes to `a`.
 */
class DestructorRetriever(private val index: SignatureIndex, private val maxCandidates: Int = 60) : PremiseRetriever {
  companion object {
    const val COST = 1.0

    /** The explicit parameter groups `(x y : T)` of a printed parameter list, as (names, type). */
    fun explicitGroups(parameters: String): List<Pair<List<String>, String>> =
      Regex("""\(([^():]+):([^()]*(?:\([^()]*\)[^()]*)*)\)""").findAll(parameters).map { m -> m.groupValues[1].trim().split(Regex("\\s+")) to m.groupValues[2].trim() }.toList()

    /** The hypothesis equations between applications of one head, with the type of their sides, and the type of the goal's sides (null unless the goal is an equation). */
    fun shapes(goal: ArendGoal): List<Pair<Symbol, Symbol?>> {
      // The type the equation compares in, `Nat` for `x = {Nat} y` between elements of `Fin n`, rather than the sides' own
      fun typeOf(equation: Expression, side: Expression) = (RewriteGenerator.equationType(equation) ?: side.type)?.let { PremiseRetriever.head(it) }
      val goalType = RewriteGenerator.equationSides(goal.expectedType)?.let { (left, _) -> typeOf(goal.expectedType, left) }
      return goal.typechecker.context.values.mapNotNull { binding ->
        val (a, b) = RewriteGenerator.equationSides(binding.type) ?: return@mapNotNull null
        val head = PremiseRetriever.headKey(a) ?: return@mapNotNull null
        if (head != PremiseRetriever.headKey(b)) return@mapNotNull null
        val sideType = typeOf(binding.type, a) ?: return@mapNotNull null
        sideType to goalType
      }.distinct()
    }
  }

  /** The symbols searched for a goal: the types of the sides of its same-headed hypothesis equations. */
  fun symbols(goal: ArendGoal): List<Symbol> = shapes(goal).map { it.first }.distinct()

  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> {
    // Candidates with their rank: destructors take one argument (`pred`, `iabs`), so functions with fewer
    // explicit parameters come first, and among them the ones named shortest (`pred` before `powSum`)
    val candidates = LinkedHashMap<Pair<String, String>, Pair<PremiseCandidate, Pair<Int, Int>>>()
    for ((sideType, goalType) in shapes(goal)) {
      for (entry in index.bySymbol(sideType)) {
        if (!entry.text.trim().startsWith("\\func")) continue
        if (entry.codomain.size > 2 || (goalType != null && entry.codomain.firstOrNull()?.let { goalType.matches(it) } != true)) continue
        val groups = explicitGroups(entry.parameters)
        val last = groups.lastOrNull() ?: continue
        if (last.first.size != 1 || !sideType.matches(last.second.substringBefore(' '))) continue
        candidates.putIfAbsent(entry.module to entry.name, PremiseCandidate(entry.name, entry.module, COST) to (groups.sumOf { it.first.size } to entry.name.length))
      }
    }
    return candidates.values.sortedWith(compareBy({ it.second.first }, { it.second.second })).map { it.first }.take(maxCandidates)
  }
}
