package typechecker.coreapi.proofstep

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
import org.arend.core.subst.ExprSubstitution
import org.arend.ext.core.level.LevelSubstitution
import org.arend.ext.concrete.definition.FunctionKind
import org.arend.ext.concrete.expr.ConcreteArgument
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.term.concrete.Concrete
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof

import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.Precedence
import org.arend.naming.reference.FullModuleReferable
import org.arend.naming.reference.LocalReferable
import org.arend.server.ArendServer

class AppGenerator(private val server: ArendServer, private val premises: List<CallableDefinition>, private val moduleLocation: ModuleLocation): ProofStepGenerator<ArendGoal> {

  class Premise(val def: CallableDefinition) {
    fun toExpression(typechecker: CheckTypeVisitor, goal: ArendGoal): Expression {
      val levels = def.makeIdLevels()
      return when (def) {
        is FunctionDefinition -> etaExpand(def)
        is ClassField -> {
          val thisType = def.parentClass.getDefCall(def.parentClass.makeIdLevels(), emptyList<Expression>())
          val thisArg = typechecker.generateNewInferenceVariable("this", thisType, goal.sourceNode, true) as Expression
          FieldCallExpression.make(def, thisArg)
        }
        is Constructor -> {
          val dataParams = mutableListOf<DependentLink>()
          def.dataType.getTypeWithParams(dataParams, def.dataType.makeIdLevels())
          val dataArgs = dataParams.map { typechecker.generateNewInferenceVariable(it.name, it.type, goal.sourceNode, true) as Expression }
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

      val singleParameters = mutableListOf<SingleDependentLink>()
      val paramsList = DependentLink.Helper.toList(parameters)

      var result: SingleDependentLink = EmptyDependentLink.getInstance()
      val substitution = ExprSubstitution()
      for (link in paramsList.asReversed()) {
        result = TypedSingleDependentLink(
          link.isExplicit,
          link.name,
          link.type.subst(substitution, LevelSubstitution.EMPTY),
          false
        )
        singleParameters.add(result)
        substitution.add(link, listOf(ReferenceExpression(result)))
      }
      singleParameters.reverse()

      val args = singleParameters.map { ReferenceExpression(it) }

      var body = def.getDefCall(levels, args)

      singleParameters.reverse()
      for (param in singleParameters) {
        body = LamExpression(param, body)
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

    for (param in concreteDef.parameters) {
      if (args.size == numArgsToAdd) {
        break
      }
      if (param.isExplicit) {
        val paramType = coreParam.type.normalize(NormalizationMode.WHNF) as? UniverseExpression
        if (paramType != null && paramType.sortExpression.isProp) {
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

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val result = mutableListOf<ProofStep<ArendGoal>>()
    val expectedType = goal.expectedType
    val typechecker = goal.typechecker
    val factory = typechecker.factory

    for (premise in premises) {
      val funcType = Premise(premise).toExpression(typechecker, goal).computeType()

      val expectedArity = getArity(expectedType)
      val funcArity = getArity(funcType)
      val numArgsToAdd = funcArity - expectedArity

      val concreteApp = createConcreteApp(premise, typechecker, numArgsToAdd)

      if (concreteApp != null) {
        val context = typechecker.saveTypecheckingContext()
        val branchTC = CheckTypeVisitor.loadTypecheckingContext(context, ListErrorReporter())
        val appExpr = branchTC.typecheck(concreteApp, expectedType)
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
              factory.core(goal.expectedType.computeTyped()),
              null,
              factory.body(concreteExpr)
            ) as Concrete.FunctionDefinition,
            ArendGoal(goal.expectedType, branchTC, goal.sourceNode)
          )
          result.add(ProofStep(resultProof, 1.0))
        }
      }
    }

    return result
  }
}
