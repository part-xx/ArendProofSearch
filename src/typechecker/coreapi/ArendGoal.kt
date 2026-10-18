package typechecker.coreapi

import typechecker.coreapi.proofstep.RewriteGenerator

import org.arend.core.definition.Definition
import org.arend.core.expr.Expression
import org.arend.term.concrete.Concrete
import org.arend.typechecking.visitor.CheckTypeVisitor
import typechecker.Goal

/**
 * A goal: its expected type, the typechecker holding its local context, and the source node of
 * the `{?}` it came from. [definition] is the definition being proved, which the typechecker of a
 * goal inside a branch does not know.
 */
class ArendGoal(
  /** The type as the typechecker reported it, possibly with inference variables solved only after the report. */
  private val rawType: Expression,
  val typechecker: CheckTypeVisitor,
  val sourceNode: Concrete.Expression,
  val definition: Definition? = typechecker.definition,
): Goal<ArendGoal>() {
  /**
   * The type to prove, read when the generators need it, after the typechecking that produced the
   * goal has finished: solved inference variables are replaced by their solutions and a lambda at
   * the head is applied ([betaReduced]).
   */
  val expectedType: Expression by lazy { betaReduced(rawType) }

  private val problem: String by lazy { toString() }

  /** The statement over its context, as printed: what a step's success depends on. */
  val problemText: String get() = problem

  // An equation's type is printed too: `x = {Nat} y` and `x = y` in `Fin n` print alike, and are different problems
  // (`fin_nat-inj` turns one into the other, which must not look like a regress)
  override fun toString(): String {
    val equationType = RewriteGenerator.equationType(expectedType)?.let { " in type $it" } ?: ""
    return "$expectedType$equationType in context ${typechecker.context.values.joinToString { "${it.name} : ${it.type}" }}"
  }

  /** The same statement over the same context, as printed; a proof step that fills one fills the other. */
  override fun isSameProblem(other: ArendGoal): Boolean = this === other || problem == other.problem
}
