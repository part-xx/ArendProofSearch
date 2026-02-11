package typechecker.impl.proofstep

import org.arend.core.context.param.DependentLink
import org.arend.core.context.param.EmptyDependentLink
import org.arend.core.context.param.SingleDependentLink
import org.arend.core.context.param.TypedSingleDependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.Constructor
import org.arend.core.definition.FunctionDefinition
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.core.expr.*
import org.arend.core.sort.Sort
import org.arend.core.subst.ExprSubstitution
import org.arend.core.subst.SubstVisitor
import org.arend.ext.concrete.definition.FunctionKind
import org.arend.ext.concrete.expr.ConcreteArgument
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.CMP
import org.arend.ext.core.ops.NormalizationMode
import org.arend.term.concrete.Concrete
import typechecker.ProofStepGenerator
import typechecker.impl.ArendGoal
import typechecker.impl.ArendProof

import org.arend.ext.core.level.LevelSubstitution
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.Precedence
import org.arend.naming.reference.FullModuleReferable
import org.arend.naming.reference.LocalReferable
import org.arend.naming.reference.TCDefReferable
import org.arend.server.ArendServer
import typechecker.Goal

class AppGenerator(private val server: ArendServer, private val premises: List<CallableDefinition>, private val moduleLocation: ModuleLocation): ProofStepGenerator {

  class Premise(val def: CallableDefinition) {
    fun toExpression(typechecker: CheckTypeVisitor, goal: ArendGoal): Expression {
      val levels = def.makeIdLevels()
      return when (def) {
        is FunctionDefinition -> etaExpand(def) // def.getDefCall(levels, emptyList())
        is ClassField -> {
          val thisType = def.parentClass.getDefCall(def.parentClass.makeIdLevels(), emptyList<Expression>())
          val thisArg = typechecker.generateNewInferenceVariable("this", thisType, goal.sourceNode, true) as Expression
          FieldCallExpression.make(def, thisArg)
        }
        is Constructor -> {
          val dataParams = mutableListOf<DependentLink>()
          def.dataType.getTypeWithParams(dataParams, def.dataType.makeIdLevels())
          val dataArgs = dataParams.map { typechecker.generateNewInferenceVariable(it.name, it.typeExpr, goal.sourceNode, true) as Expression }
          ConCallExpression.make(def, levels, dataArgs, emptyList<Expression>())
        }
        else -> def.getDefCall(levels, emptyList<Expression>())
      }
    }

    fun etaExpand(def: FunctionDefinition): Expression {
      val levels = def.makeIdLevels()
      val parameters = def.parameters
      if (!parameters.hasNext()) {
        return def.getDefCall(levels, emptyList())
      }

      // Convert DependentLink to SingleDependentLink for LamExpression
      val singleParameters = mutableListOf<SingleDependentLink>()
      // Reconstruct as SingleDependentLink if it's a chain of multiple blocks
      val paramsList = DependentLink.Helper.toList(parameters)
      // val names = paramsList.map { it.name }
      // Note: This assumes they can be grouped.
      // If types differ, you may need nested Lambdas instead of a single SingleDependentLink block.
      // For eta-expansion of a function, recreating the parameters 1-by-1 is safest.

      var result: SingleDependentLink = EmptyDependentLink.getInstance()
      val substitution = ExprSubstitution()
      for (link in paramsList.asReversed()) {
        result = TypedSingleDependentLink(
          link.isExplicit,
          link.name,
          link.type.subst(SubstVisitor(substitution, LevelSubstitution.EMPTY)),
          false
        )
        singleParameters.add(result)
        substitution.add(link, listOf(ReferenceExpression(result)))
      }
      singleParameters.reverse()

      // Create arguments for the function call
      val args = singleParameters.map { ReferenceExpression(it) }

      var body = def.getDefCall(levels, args)
      val resultSort = body.computeType().toSort() ?: Sort.SET0

      singleParameters.reverse()
      for (param in singleParameters) {
        body = LamExpression(resultSort, param, body)
      }

      return body
    }
  }

  private fun createConcreteApp(def: CallableDefinition, typechecker: CheckTypeVisitor, numArgsToAdd: Int): ConcreteExpression? {
    val tcReferable = def.ref
    val definitionData = server.getResolvedDefinition(tcReferable)
    val concreteDef = definitionData?.definition ?: return null
    var coreParam = def.parameters
    val factory = typechecker.factory
    val args = mutableListOf<ConcreteArgument>()
    // var coreCurrentVar = 0
    // var coreCurrentSize = DependentLink.Helper.size(coreParam)

    for (param in concreteDef.parameters) {
      if (args.size == numArgsToAdd) {
        break
      }
      if (param.isExplicit) {
        val paramType = coreParam.typeExpr.type
        if (paramType is UniverseExpression && paramType.sort == Sort.PROP) {
          for (i in 0..<param.refList.size) {
            args.add(factory.arg(factory.goal(), true))
          }
        } else {
          for (i in 0..<param.refList.size) {
            args.add(factory.arg(factory.hole(), true))
          }
        }
      }
      coreParam = coreParam.next
      /*
      if (coreCurrentVar < coreCurrentSize - 1) {
        ++coreCurrentVar
      } else {

        coreCurrentSize = DependentLink.Helper.size(coreParam)
        coreCurrentVar = 0
      }*/
    }

    return factory.app(factory.ref(def.ref), args)
  }


  private fun getArity(expression: Expression): Int {
    var type = expression.normalize(NormalizationMode.WHNF)
    var arity = 0
    while (type is PiExpression) {
      if (type.parameters.isExplicit) {
        arity += DependentLink.Helper.size(type.parameters)
      }
      type = type.codomain.normalize(NormalizationMode.WHNF)
    }
    return arity
  }

  override fun generate(goal: Goal): List<ArendProofStep> {
    val goalArd = goal as? ArendGoal ?: return emptyList()
    val result = mutableListOf<ArendProofStep>()
    val expectedType = goalArd.expectedType
    val typechecker = goalArd.typechecker
    val factory = typechecker.factory
    // val tcBackupContext = typechecker.context

    // typechecker.copyContextFrom(goalArd.context)

    for (premise in premises) {
      val funcType = Premise(premise).toExpression(typechecker, goalArd).computeType()

      val expectedArity = getArity(expectedType)
      val funcArity = getArity(funcType)
      val numArgsToAdd = funcArity - expectedArity

      val concreteApp = createConcreteApp(premise, typechecker, numArgsToAdd)
      /*if (numArgsToAdd >= 0) {
        var currentFunc = func
        var currentFuncType = funcType
        var ok = true
        for (i in 0..<numArgsToAdd) {
          currentFuncType = currentFuncType.normalize(NormalizationMode.WHNF)
          val pi = currentFuncType as? PiExpression
          if (pi == null) {
            ok = false
            break
          }
          val parameters = pi.parameters
          val arg = tc.generateNewInferenceVariable(parameters.name ?: "arg", parameters.typeExpr, goalArd.sourceNode, true) as Expression
          currentFunc = AppExpression.make(currentFunc, arg, parameters.isExplicit)
          currentFuncType = pi.applyExpression(arg)
        }*/

      if (concreteApp != null) {
        val context = typechecker.saveTypecheckingContext()
        val branchTC = CheckTypeVisitor.loadTypecheckingContext(context, ListErrorReporter())
        val appExpr = branchTC.typecheck(concreteApp, expectedType)
          // typechecker.typecheck(concreteApp, expectedType)
        //if (tc.compare(currentFuncType, expectedType, CMP.LE, goalArd.sourceNode, true, true, true)) {
        if (!branchTC.status.hasErrors() && appExpr != null) {
          val concreteExpr = factory.core(appExpr)
          val concreteParameters =
            branchTC.context.map { Concrete.NameParameter(it.value, true, LocalReferable(it.value.name)) }
          val moduleRef = FullModuleReferable(moduleLocation)

          val functionRef = factory.global(
            moduleRef,
            "goal" + goal.hashCode(),
            Precedence.DEFAULT,
            null,
            null
          )
          val resultProof = ArendProof(
            factory.function(
              functionRef,
              FunctionKind.FUNC,
              concreteParameters,
              factory.core(goalArd.expectedType.computeTyped()),
              null,
              factory.body(concreteExpr)
            ) as Concrete.FunctionDefinition,
            branchTC
          )
          result.add(ArendProofStep(resultProof, 1.0))
        }
      }
    }

    // typechecker.copyContextFrom(tcBackupContext)

    return result
  }
}