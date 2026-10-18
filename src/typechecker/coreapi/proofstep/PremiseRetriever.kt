package typechecker.coreapi.proofstep

import org.arend.core.definition.Definition
import org.arend.core.expr.AppExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.PathTypeExpression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.core.ops.CMP
import org.arend.typechecking.implicitargs.equations.DummyEquations
import org.arend.ext.core.ops.NormalizationMode
import org.arend.prelude.Prelude
import typechecker.coreapi.ArendGoal

/**
 * A definition that might be applied to prove a goal.
 *
 * [name] is the definition's long name inside [module]; with no [module] it is resolved in the
 * scope of the module being proved. Candidates with a lower [cost] are tried first.
 */
data class PremiseCandidate(val name: String, val module: String? = null, val cost: Double = 1.0)

/** A retrieval heuristic: selects the premises worth trying for a goal. */
interface PremiseRetriever {
  fun retrieve(goal: ArendGoal): List<PremiseCandidate>

  companion object {
    /** A proof search query at least this slow is logged. */
    const val SLOW_QUERY_MILLIS = 10_000L

    /**
     * The definition at the head of [type], looking through Pi codomains and applications, or
     * null if the head is not a definition (e.g. a local variable).
     */
    fun head(type: Expression): Symbol? {
      fun head(expr: Expression): Symbol? {
        var current = expr
        while (true) {
          current = when (val e = current) {
            is PiExpression -> e.codomain
            is AppExpression -> e.function
            else -> break
          }
        }
        // `a = b` is written with the infix `=`, which unfolds to Path
        if (current is PathTypeExpression) return Symbol.of(Prelude.PATH_INFIX)
        val definition = (current as? DefCallExpression)?.definition ?: return null
        return Symbol.of(if (definition == Prelude.PATH) Prelude.PATH_INFIX else definition)
      }
      return head(type) ?: head(type.normalize(NormalizationMode.WHNF))
    }

    /** The name of [head]. */
    fun headName(type: Expression): String? = head(type)?.name

    /** What [type] is about: the definition at its head, or the variable there, as `P` in `P a`; null for other types. */
    fun headKey(type: Expression): Any? {
      head(type)?.let { return it }
      var current = type.normalize(NormalizationMode.WHNF)
      while (true) {
        current = when (val e = current) {
          is PiExpression -> e.codomain.normalize(NormalizationMode.WHNF)
          is AppExpression -> e.function
          else -> break
        }
      }
      return (current as? ReferenceExpression)?.binding
    }

    /** Whether two expressions are equal up to normalization. */
    fun same(a: Expression, b: Expression): Boolean = CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, a, b, null, null)
  }
}

/**
 * A definition as the CLI's proof search sees it: patterns have to use its [name], while results
 * print it by its [alias] when it has one (the field `meet` is printed `∧`).
 */
data class Symbol(val name: String, val alias: String? = null) {
  private val spellings = listOfNotNull(name, alias)

  /** Whether [token] of a printed result is this symbol; the CLI may qualify names. */
  fun matches(token: String): Boolean = spellings.any { token == it || token.endsWith(".$it") }

  /** Whether this symbol occurs somewhere inside [text] as a whole name: `Pos` does not occur in `PosPair`. */
  fun occursIn(text: String): Boolean = spellings.any { spelling ->
    generateSequence(text.indexOf(spelling)) { text.indexOf(spelling, it + 1) }.takeWhile { it >= 0 }.any { at ->
      val before = text.getOrNull(at - 1)
      val after = text.getOrNull(at + spelling.length)
      (before == null || !isNameChar(before)) && (after == null || !isNameChar(after))
    }
  }

  private fun isNameChar(c: Char) = c.isLetterOrDigit() || c == '_' || c == '\'' || c == '-'

  companion object {
    fun of(definition: Definition) = Symbol(definition.ref.refName, definition.ref.aliasName)
  }
}

/** The same premises for every goal. */
class FixedPremiseRetriever(private val names: List<String>) : PremiseRetriever {
  override fun retrieve(goal: ArendGoal): List<PremiseCandidate> = names.map { PremiseCandidate(it) }
}
