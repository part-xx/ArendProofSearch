import org.arend.core.expr.Expression
import org.arend.ext.error.ErrorReporter
import org.arend.term.concrete.Concrete
import org.arend.typechecking.TypecheckingContext
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.CheckTypeVisitor
import typechecker.coreapi.ArendGoal

class FindGoalsVisitor(typecheckingContext: TypecheckingContext,
                       val sourceNode: Concrete.Expression,
                       errorReporter: ErrorReporter
): CheckTypeVisitor(
  typecheckingContext.localContext(),
  typecheckingContext.localPrettifier(),
  errorReporter,
  typecheckingContext.instancePool(),
  typecheckingContext.arendExtension(),
  typecheckingContext.resolveListener(),
  typecheckingContext.userDataHolder()
) {
  private val goalExpressions: MutableMap<ArendGoal, Concrete.Expression> = HashMap()

  fun getGoals(): Map<ArendGoal, Concrete.Expression> = goalExpressions

  override fun visitGoal(expr: Concrete.GoalExpression, expectedType: Expression?): TypecheckingResult? {
    val currentContext: TypecheckingContext? = saveTypecheckingContext()
    val goal = ArendGoal(expectedType!!, loadTypecheckingContext(currentContext, errorReporter), sourceNode)
    goalExpressions[goal] = expr
    return super.visitGoal(expr, expectedType)
  }

}