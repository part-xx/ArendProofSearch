package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.expr.AppExpression
import org.arend.core.expr.ConCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FieldCallExpression
import org.arend.core.expr.IntegerExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.ext.concrete.ConcreteFactory
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.naming.reference.Referable
import typechecker.coreapi.ArendGoal

/**
 * Writes a core expression of a goal as a concrete term over the goal's context, for use inside a
 * proof step: `Big {_} {_} (∧ {L}) x l` for the core `Big {L.E} {L.E} (L.∧) x l`.
 *
 * Embedding the core expression itself (`factory.core`) only works at the top of a proof: inside a
 * `\case` clause, the pattern variables are bound afresh each time the proof is typechecked, so a
 * core expression referring to them goes stale as soon as the step is plugged into the proof.
 * Implicit arguments are left to inference; expressions this does not cover give null.
 */
object CoreToConcrete {
  fun convert(expression: Expression, goal: ArendGoal): ConcreteExpression? =
    convert(expression, StepBuilder.context(goal).associate { it.second to it.first }, goal.typechecker.factory)

  /** [convert] with the subterms in [replacements], by identity, converted to the given expressions: the motive `\lam z => n mod m <= z` of a transport. */
  fun convert(expression: Expression, context: Map<Binding, Referable>, factory: ConcreteFactory, replacements: java.util.IdentityHashMap<Expression, ConcreteExpression> = java.util.IdentityHashMap()): ConcreteExpression? {
    fun convert(expr: Expression): ConcreteExpression? {
      replacements[expr]?.let { return it }
      return when (expr) {
      is ReferenceExpression -> context[expr.binding]?.let { factory.ref(it) }
      // A solved inference variable stands for its solution
      is org.arend.core.expr.InferenceReferenceExpression -> expr.substExpression?.let { convert(it) }
      is IntegerExpression -> factory.number(expr.bigInteger)
      is FieldCallExpression -> convert(expr.argument)?.let { factory.app(factory.ref(expr.definition.ref), listOf(factory.arg(it, false))) }
      is ConCallExpression -> {
        // The data type's arguments are implicit and inferred; the constructor's own follow
        val params = DependentLink.Helper.toList(expr.definition.parameters)
        val arguments = expr.dataTypeArguments.map { factory.arg(factory.hole(), false) } +
          params.zip(expr.defCallArguments).map { (param, arg) -> factory.arg(if (param.isExplicit) convert(arg) ?: return null else factory.hole(), param.isExplicit) }
        factory.app(factory.ref(expr.definition.ref), arguments)
      }
      is DefCallExpression -> {
        val params = DependentLink.Helper.toList(expr.definition.parameters)
        if (params.size != expr.defCallArguments.size) return null
        val arguments = params.zip(expr.defCallArguments).map { (param, arg) -> factory.arg(if (param.isExplicit) convert(arg) ?: return null else factory.hole(), param.isExplicit) }
        factory.app(factory.ref(expr.definition.ref), arguments)
      }
      is AppExpression -> {
        val function = convert(expr.function) ?: return null
        val argument = convert(expr.argument) ?: return null
        factory.app(function, listOf(factory.arg(argument, expr.isExplicit)))
      }
      else -> null
      }
    }
    return convert(expression)
  }
}
