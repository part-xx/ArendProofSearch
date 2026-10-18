package typechecker.coreapi.proofstep

import org.arend.core.expr.Expression
import org.arend.core.expr.FieldCallExpression
import org.arend.core.expr.FunCallExpression
import org.arend.core.expr.UniverseExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.core.expr.visitor.VoidExpressionVisitor
import org.arend.ext.core.definition.CoreFunctionDefinition
import org.arend.prelude.Prelude
import typechecker.cli.CliApi
import typechecker.coreapi.ArendGoal

/**
 * Retrieves library equations to rewrite with, from the Arend CLI's proof search for `=`
 * ([SignatureIndex]): for every function `f` applied in the goal, the definitions whose codomain
 * is an equation and whose signature mentions `f`. Equations with a side headed by `f` (`f ... = ...`, as
 * `+-comm`, `ide-left`, `-'0`) come first; the others mention `f` deeper inside.
 */
class EquationRetriever(
  private val index: SignatureIndex, private val maxCandidates: Int = 5000, private val maxSymbols: Int = 5,
  /** Candidates left out, e.g. the lemma being proved in a benchmark. */
  private val excluded: (PremiseCandidate) -> Boolean = { false },
) : PremiseRetriever {
  constructor(cli: CliApi, maxCandidates: Int = 5000, maxSymbols: Int = 5) : this(SignatureIndex(cli), maxCandidates, maxSymbols)

  companion object {
    const val SIDE_HEAD_COST = 1.5
    const val INSIDE_COST = 2.0
    /** Added for each operator of the equation that the goal does not contain, e.g. `*` in `ldistr` for a goal about `+`. */
    const val FOREIGN_OPERATOR_COST = 0.5

    /** Prelude's equations, by the functions they are about; `-ps` only searches libraries. */
    val PRELUDE_EQUATIONS = mapOf("Nat.divModProp" to setOf("mod", "div"))

    /** Whether [token] is an infix operator such as `+`, `-'` or `∧`, rather than a name or a variable. */
    fun isOperator(token: String): Boolean = token.isNotEmpty() && token.none { it.isLetterOrDigit() } && token != "=" && token != "->"

    /** The functions applied in [type], outermost first. */
    fun functionNames(type: Expression): List<String> = functionSymbols(type).map { it.name }

    /** The functions applied in [type], outermost first. */
    fun functionSymbols(type: Expression): List<Symbol> {
      val names = LinkedHashSet<Symbol>()
      type.accept(object : VoidExpressionVisitor<Void?>() {
        override fun visitFunCall(expr: FunCallExpression, params: Void?): Void? {
          // Instances such as `NatSemiring` are arguments of the operators, not operators themselves
          if (expr.definition != Prelude.PATH_INFIX && expr.definition.kind != CoreFunctionDefinition.Kind.INSTANCE) {
            names.add(Symbol.of(expr.definition))
          }
          return super.visitFunCall(expr, params)
        }

        override fun visitFieldCall(expr: FieldCallExpression, params: Void?): Void? {
          // A field whose value is a type, such as the carrier `E` of an order, is not an operation
          if (expr.definition.type.codomain.normalize(NormalizationMode.WHNF) !is UniverseExpression) {
            names.add(Symbol.of(expr.definition))
          }
          return super.visitFieldCall(expr, params)
        }
      }, null)
      return names.toList()
    }

    /**
     * The cost of rewriting with an equation whose codomain is [codomain] in a goal applying
     * [goalSymbols], found by searching for [symbol]; null if it is not an equation.
     */
    fun equationCost(codomain: List<String>, symbol: Symbol, goalSymbols: Collection<Symbol>): Double? {
      val equals = codomain.indexOf("=")
      if (equals <= 0 || equals == codomain.size - 1) return null
      val left = codomain.subList(0, equals)
      val right = codomain.subList(equals + 1, codomain.size)
      // `f a b = ...`, or an infix `a f b = ...`
      fun headed(side: List<String>) = symbol.matches(side.first()) || (side.size == 3 && symbol.matches(side[1]))
      val foreignOperators = codomain.filter(::isOperator).toSet().count { operator -> goalSymbols.none { it.matches(operator) } }
      return (if (headed(left) || headed(right)) SIDE_HEAD_COST else INSIDE_COST) + foreignOperators * FOREIGN_OPERATOR_COST
    }

    fun equationCost(codomain: List<String>, symbol: String, goalSymbols: Collection<String> = listOf(symbol)): Double? =
      equationCost(codomain, Symbol(symbol), goalSymbols.map { Symbol(it) })
  }

  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> = retrieve(goal, includeHypotheses = false)

  /**
   * The equations for the goal's functions and, with [includeHypotheses], for those of its hypotheses too:
   * a transport may bring a hypothesis's form to the goal (`negative-isInv` for `p : negative y <= negative x`).
   * Prelude's equations are not found by the CLI's proof search and are added by hand ([PRELUDE_EQUATIONS]).
   */
  fun retrieve(goal: ArendGoal, includeHypotheses: Boolean): List<PremiseCandidate> {
    // Each candidate with its rank among the equations of its symbol
    val candidates = mutableListOf<Pair<PremiseCandidate, Int>>()
    val goalSymbols = functionSymbols(goal.expectedType) +
      (if (includeHypotheses) goal.typechecker.context.values.flatMap { functionSymbols(it.type).take(2) } else emptyList())
    val equations = index.bySymbol(Symbol("="))
    for ((name, about) in PRELUDE_EQUATIONS) {
      if (goalSymbols.any { symbol -> about.any { symbol.matches(it) } }) candidates.add(PremiseCandidate(name, null, INSIDE_COST) to 0)
    }
    for (symbol in goalSymbols.distinct().take(if (includeHypotheses) 2 * maxSymbols else maxSymbols)) {
      val forSymbol = equations.filter { symbol.occursIn(it.text) }.mapNotNull { entry ->
        val cost = equationCost(entry.codomain, symbol, goalSymbols) ?: return@mapNotNull null
        PremiseCandidate(entry.name, entry.module, cost)
      }.sortedBy { it.cost }
      forSymbol.forEachIndexed { rank, candidate -> candidates.add(candidate to rank) }
    }
    // Equal costs are interleaved by rank, so that a symbol with many equations (`+`) does not crowd out the others
    return candidates
      .groupBy { (candidate, _) -> candidate.module to candidate.name }
      .map { (_, sameDefinition) -> sameDefinition.minWith(compareBy({ it.first.cost }, { it.second })) }
      .sortedWith(compareBy({ it.first.cost }, { it.second }))
      .map { it.first }
      .filterNot(excluded)
      .take(maxCandidates)
  }
}
