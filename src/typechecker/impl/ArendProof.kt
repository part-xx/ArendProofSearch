package typechecker.impl

import FindGoalsVisitor
import org.arend.core.context.binding.Binding
import org.arend.core.definition.FunctionDefinition
import org.arend.core.elimtree.ElimBody
import org.arend.core.elimtree.LeafElimTree
import org.arend.core.expr.ErrorExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.error.ArgInferenceError
import org.arend.ext.error.ErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.typechecking.ExpressionTypechecker
import org.arend.naming.reference.LocalReferable
import org.arend.term.concrete.BaseConcreteExpressionVisitor
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.SearchConcreteVisitor
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.typechecking.visitor.DefinitionTypechecker
import org.arend.typechecking.visitor.SearchVisitor
import typechecker.Goal
import typechecker.Proof

open class ArendProof(private val theorem: Concrete.FunctionDefinition, private val typechecker: CheckTypeVisitor): Proof {
  private val goalExpressions: Map<ArendGoal, Concrete.Expression>
  private val definitionTypechecker = DefinitionTypechecker(typechecker, null)

  init {
    val proof = getProof()
    if (proof != null) {
      goalExpressions = findGoals(proof, typechecker)
    } else {
      goalExpressions = HashMap()
    }
  }

  fun getGoals(): Map<ArendGoal, Concrete.Expression> = goalExpressions

  fun getProof(): Concrete.Expression? = theorem.body.term

  companion object {
    fun findGoals(proof: Concrete.Expression, typechecker: CheckTypeVisitor): Map<ArendGoal, Concrete.Expression> {
      val context = typechecker.saveTypecheckingContext()
      val goalsVisitor = FindGoalsVisitor(context, proof, ListErrorReporter())
      proof.accept(goalsVisitor, null)
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

  override fun replaceGoal(goal: Goal, proof: Proof): ArendProof? {
    val goalArd = goal as? ArendGoal ?: return null
    val proofArd = proof as? ArendProof ?: return null
    val goalExpr = goalExpressions[goalArd] ?: return null

    val newProof = getProof()?.accept(object: BaseConcreteExpressionVisitor<Void>() {
      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression? {
        if (expr == goalExpr) {
          return proofArd.getProof()
        }
        return super.visitGoal(expr, params)
      }
    }, null) ?: return null
    val newTheorem = typechecker.factory.function(theorem.ref, theorem.kind, theorem.parameters, theorem.resultType, theorem.resultTypeLevel, typechecker.factory.body(newProof)) as? Concrete.FunctionDefinition ?: return null
    var withErrors = false
    val errorReporter = ErrorReporter { e -> if (e !is ArgInferenceError) withErrors = true }

    typechecker.withErrorReporter(errorReporter) { _ -> newTheorem.accept(definitionTypechecker, null) }

    if (withErrors) {
      return null
    }

    //val elimBody = ((typechecker.definition as? FunctionDefinition)?.body as? ElimBody) ?: return null
    // val elimTree = elimBody.elimTree as? LeafElimTree ?: return null
    // val checkedProof = elimBody.clauses[elimTree.clauseIndex].expression ?: return null

    return ArendProof(newTheorem, typechecker)
  }
}