package typechecker.coreapi

import FindGoalsVisitor
import org.arend.core.context.binding.Binding
import org.arend.core.expr.Expression
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.ext.error.ArgInferenceError
import org.arend.ext.error.ErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.term.concrete.BaseConcreteExpressionVisitor
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.SubstConcreteVisitor
import org.arend.typechecking.visitor.DefinitionTypechecker
import typechecker.Proof

open class ArendProof(private val theorem: Concrete.FunctionDefinition, private val goal: ArendGoal): Proof<ArendGoal> {
  private val goalExpressions: Map<ArendGoal, Concrete.Expression>
  private val definitionTypechecker = DefinitionTypechecker(goal.typechecker, emptySet())

  init {
    val proof = getProof()
    if (proof != null) {
      goalExpressions = findGoals(proof, goal)
    } else {
      goalExpressions = HashMap()
    }
  }

  fun getGoals(): Map<ArendGoal, Concrete.Expression> = goalExpressions

  fun getProof(): Concrete.Expression? = theorem.body.term

  override fun toString(): String {
    return getProof().toString()
  }

  companion object {
    fun findGoals(proof: Concrete.Expression, goal: ArendGoal): Map<ArendGoal, Concrete.Expression> {
      val context = goal.typechecker.saveTypecheckingContext()
      val goalsVisitor = FindGoalsVisitor(context, proof, ListErrorReporter())
      proof.accept(goalsVisitor, goal.expectedType)
      return goalsVisitor.getGoals()
    }

    fun extractContext(expression: Expression, context: MutableSet<Binding>) {
      val exprQueue = ArrayDeque<Expression>(listOf(expression, expression.type))
      while (exprQueue.isNotEmpty()) {
        val expr = exprQueue.removeFirst()
        val exprContext = FreeVariablesCollector.getFreeVariables(expr)
        for (binding in exprContext) {
          if (context.contains(binding)) { continue }
          context.add(binding)
          exprQueue.addLast(binding.typeExpr)
        }
      }
    }
  }

  override fun goals(): List<ArendGoal> {
    return goalExpressions.keys.toList()
  }

  override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): ArendProof? {
    val proofArd = proof as? ArendProof ?: return null
    val goalExpr = goalExpressions[goal] ?: return null

    val substVisitor = SubstConcreteVisitor(null)
    val goalContext = goal.typechecker.context
    for (param in proofArd.theorem.parameters) {
      for (ref in param.referableList) {
        if (ref != null) {
          val matchingEntry = goalContext.entries.find { it.value.name == ref.refName }
          if (matchingEntry != null) {
            substVisitor.bind(ref, matchingEntry.key)
          }
        }
      }
    }
    val substitutedProof = proofArd.getProof()?.accept(substVisitor, null)

    val newProof = getProof()?.accept(object: BaseConcreteExpressionVisitor<Void>() {
      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression? {
        if (expr == goalExpr) {
          return substitutedProof
        }
        return super.visitGoal(expr, params)
      }
    }, null) ?: return null
    val newTheorem = goal.typechecker.factory.function(theorem.ref, theorem.kind, theorem.parameters, theorem.resultType, theorem.resultTypeLevel, goal.typechecker.factory.body(newProof)) as? Concrete.FunctionDefinition ?: return null
    var withErrors = false
    val errorReporter = ErrorReporter { e -> if (e !is ArgInferenceError) withErrors = true }

    goal.typechecker.withErrorReporter(errorReporter) { _ -> newTheorem.accept(definitionTypechecker, null) }

    if (withErrors) {
      return null
    }

    return ArendProof(newTheorem, this.goal)
  }
}
