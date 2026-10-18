package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.ClassDefinition
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.AppExpression
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FieldCallExpression
import org.arend.core.expr.NewExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.naming.reference.Referable
import typechecker.coreapi.ArendGoal

/**
 * Retrieves lemmas of a twin structure for a goal, as arend-lib proves a monoid's `BigProd_suc` by
 * `AddMonoid.BigSum_suc {AddMonoid.fromMonoid \this}` and a group's `inverse-isInv` by
 * `AddGroup.negative-isInv {AddGroup.fromGroup \this}`: for each class instance `A : C` of the context
 * and each conversion `C -> D` of arend-lib (`fromMonoid`, `fromGroup`, `toGroup`, a lattice's `toMonoid`),
 * the lemmas found for the twin names of the goal's symbols under the conversion (`*` for `+`, `ide` for
 * `zro`, read off the conversion's implementations; `BigProd` for `BigSum` by name). Such a lemma is
 * applied with its instance given, `{fromMonoid A}` ([instanceOf]); the typechecker decides whether the
 * conclusion computes to the goal.
 */
class TransferRetriever(private val index: SignatureIndex, private val conversions: List<Conversion>, private val maxCandidates: Int = 60) : PremiseRetriever {
  /** A conversion function from instances of [from] to instances of [to], with the twin names it induces (a name of [to] for each name of [from] and back). */
  class Conversion(val function: FunctionDefinition, val from: ClassDefinition, val to: ClassDefinition, val twins: Map<String, String>)

  companion object {
    const val COST = 1.2
    /** Twins that are not fields: functions defined alike over the twin operations. */
    val NAMED_TWINS = listOf("BigProd" to "BigSum", "BigJoin" to "BigSum", "BigMeet" to "BigProd", "pow" to "*n")

    /** The conversion [function], as `AddMonoid.fromMonoid`, read: its parameter's class, its result's class, and the twins its implementations show. */
    fun conversion(function: FunctionDefinition): Conversion? {
      val parameter = DependentLink.Helper.toList(function.parameters).singleOrNull { it.isExplicit } ?: return null
      val from = (parameter.type.normalize(NormalizationMode.WHNF) as? ClassCallExpression)?.definition ?: return null
      val result = function.resultType?.normalize(NormalizationMode.WHNF) as? ClassCallExpression ?: return null
      val implementations = LinkedHashMap(result.implementedHere)
      ((function.actualBody as? NewExpression)?.classCall ?: (function.actualBody as? Expression)?.normalize(NormalizationMode.WHNF)?.let { (it as? NewExpression)?.classCall })?.implementedHere?.let { implementations.putAll(it) }
      val twins = LinkedHashMap<String, String>()
      for ((field, implementation) in implementations) {
        var head: Expression = implementation
        while (head is AppExpression) head = head.function
        val source = (head as? FieldCallExpression)?.definition ?: continue
        if (source.name != field.name) { twins[source.name] = field.name; twins[field.name] = source.name }
      }
      for ((a, b) in NAMED_TWINS) { twins.putIfAbsent(a, b); twins.putIfAbsent(b, a) }
      return Conversion(function, from, result.definition, twins)
    }
  }

  /** For each candidate retrieved, the conversion and the instance of the context it applies to. */
  private val instances = HashMap<Pair<String?, String>, Pair<Conversion, Referable>>()

  /** The twin names of the goal's symbols under every conversion: what a benchmark indexes before its searches. */
  fun symbols(goal: ArendGoal): List<String> =
    (EquationRetriever.functionSymbols(goal.expectedType) + goal.typechecker.context.values.flatMap { EquationRetriever.functionSymbols(it.type).take(2) })
      .flatMap { symbol -> conversions.mapNotNull { it.twins[symbol.name] } }.distinct()

  /** The conversion and instance a candidate was retrieved for, or null for candidates of other retrievers. */
  fun instanceOf(candidate: PremiseCandidate): Pair<Conversion, Referable>? = instances[candidate.module to candidate.name]

  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> {
    // The goal's symbols and the hypotheses': `cancel-left`'s goal `y = z` says nothing, its hypothesis `x + y = x + z` does
    val symbols = (EquationRetriever.functionSymbols(goal.expectedType) + goal.typechecker.context.values.flatMap { EquationRetriever.functionSymbols(it.type).take(2) }).distinct()
    if (symbols.isEmpty()) return emptyList()
    // Ranked: the twin class's own lemmas first (`AddGroup.negative-isInv` for `fromGroup`), then those with the twin at a side's head
    val candidates = LinkedHashMap<Pair<String?, String>, Pair<PremiseCandidate, Int>>()
    for ((ref, binding) in StepBuilder.context(goal)) {
      val instanceClass = (binding.type.normalize(NormalizationMode.WHNF) as? ClassCallExpression)?.definition ?: continue
      for (conversion in conversions) {
        if (!instanceClass.isSubClassOf(conversion.from)) continue
        for (symbol in symbols) {
          val twin = conversion.twins[symbol.name] ?: continue
          val entries = index.bySymbol(twin)
          for (entry in entries) {
            if (!entry.text.trim().startsWith("\\lemma")) continue
            // Mentioning the twin, in its conclusion or in a parameter (`cancel_*-left`'s hypothesis)
            val twinSymbol = Symbol(twin)
            val inCodomain = entry.codomain.any { token -> twinSymbol.matches(token) || token.contains(twin) }
            if (!inCodomain && !twinSymbol.occursIn(entry.text)) continue
            val key = entry.module to entry.name
            val rank = (if (entry.name.startsWith(conversion.to.name + ".")) 0 else 4) + (if (entry.codomain.firstOrNull()?.let { twinSymbol.matches(it) } == true) 0 else if (inCodomain) 1 else 2)
            if (candidates.putIfAbsent(key, PremiseCandidate(entry.name, entry.module, COST) to rank) == null) instances[key] = conversion to ref
          }
        }
      }
    }
    return candidates.values.sortedBy { it.second }.map { it.first }.take(maxCandidates)
  }
}
