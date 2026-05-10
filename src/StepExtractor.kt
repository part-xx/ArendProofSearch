import org.arend.core.expr.AppExpression
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.UniverseExpression
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.ConcreteExpressionFactory

fun extractStep(proof: ConcreteExpression): ConcreteExpression? {
  if (proof is Concrete.AppExpression) {
    val newArgs = ArrayList<Concrete.Argument>()
    if (proof.function.toString() == "mcases") {
      for (arg in proof.arguments) {
        val argExpr = arg.expression
        if (argExpr is Concrete.CaseExpression) {
          newArgs.add(Concrete.Argument(processCase(argExpr), arg.isExplicit))
        } else {
          newArgs.add(arg)
        }
      }
      return Concrete.AppExpression.make(null, proof.function, newArgs)
    }

    return proof
  } else if (proof is Concrete.LamExpression) {
    val goal = ConcreteExpressionFactory.cGoal("", null)
    return ConcreteExpressionFactory.cLam(proof.parameters, goal)
  } else if (proof is Concrete.CaseExpression) {
    return processCase(proof)
  } else if (proof is Concrete.TupleExpression) {
    val fieldSteps: MutableList<Concrete.Expression> = ArrayList()
    for (field in proof.fields) {
      val fieldStep = extractStep(field) as? Concrete.Expression ?: return null
      fieldSteps.add(fieldStep)
    }
    return ConcreteExpressionFactory.cTuple(fieldSteps)
  } else if (proof is Concrete.ProjExpression) {
    val step = extractStep(proof.expression) as? Concrete.Expression ?: return null
    return ConcreteExpressionFactory.cProj(step, proof.field)
  }
  return proof
}

fun processCase(case: Concrete.CaseExpression): Concrete.CaseExpression {
  val arguments = case.arguments.map { arg ->
    val forceElim = arg.expression is Concrete.ReferenceExpression
    Concrete.CaseArgument(arg.expression, arg.referable, arg.type, arg.isElim || forceElim)
  }
  val clauses = ArrayList<Concrete.FunctionClause>()
  for (clause in case.clauses) {
    val goal = ConcreteExpressionFactory.cGoal("", null)
    clauses.add(ConcreteExpressionFactory.cClause(clause.patterns, goal))
  }
  return Concrete.CaseExpression(case.data, case.isSCase, arguments, case.resultType, case.resultTypeLevel, clauses)
}

fun getMatchedCoreArgs(args: List<Concrete.Argument>, coreArgs: List<Pair<Expression, Boolean>>): List<Expression>? {
  var concreteInd = 0
  var coreInd = 0
  val matchedArgs = ArrayList<Expression>()
  while (concreteInd < args.size && coreInd < coreArgs.size) {
    if (args[concreteInd].isExplicit && !coreArgs[coreInd].second) {
      ++coreInd
      continue
    }
    if (!args[concreteInd].isExplicit && coreArgs[coreInd].second) {
      //if (args[concreteInd].expression.toString() == "this") {
     //   ++concreteInd
     //   continue
     // }
      println("concrete implicit vs core explicit")
      return null
    }
    matchedArgs.add(coreArgs[coreInd].first)
    ++concreteInd
    ++coreInd
  }
  return matchedArgs
}

fun extractCoreArgsWithExplicitness(coreApp: Expression): List<Pair<Expression, Boolean>> {
  val args = mutableListOf<Pair<Expression, Boolean>>()
  var current: Expression? = coreApp
  while (current is AppExpression) {
    args.add(Pair(current.argument, current.isExplicit))
    current = current.function
  }

  if (current is DefCallExpression) {
    val defCallArgs = current.defCallArguments
    var curParam = current.definition.parameters
    val extraArgs = mutableListOf<Pair<Expression, Boolean>>()
    for (arg in defCallArgs) {
      extraArgs.add(Pair(arg, curParam.isExplicit))
      if (!curParam.hasNext()) {
        break
      }
      curParam = curParam.next
    }
    extraArgs.reverse()
    args.addAll(extraArgs)
  }

  args.reverse()
  return args
}
