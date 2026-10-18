package typechecker.coreapi.proofstep

import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.Constructor
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.Expression
import org.arend.core.expr.LamExpression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.UniverseExpression
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.Referable
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof

/**
 * Applies each of [premises] (functions, lemmas, constructors and class fields) to the goal. A
 * step costs the premise's entry in [premiseCosts], 1.0 by default; an application that closes the
 * goal, such as `<=-refl` or `meet-left`, costs only [CLOSING_FACTOR] of it, like closing with a
 * hypothesis, and each subgoal an application opens adds [SUBGOAL_COST].
 *
 * Besides leaving a subgoal for an argument, a hypothesis of the same kind of type is tried as the
 * argument (`triLess p`, `suc<suc x<y`): the argument may determine what the typechecker cannot
 * infer from a hole.
 */
class AppGenerator(
  private val premises: List<CallableDefinition>,
  private val moduleLocation: ModuleLocation,
  private val premiseCosts: Map<CallableDefinition, Double> = emptyMap(),
  /** A further condition on each typechecked application. */
  private val accept: ((Expression) -> Boolean)? = null,
  /** Equations applied backwards, as `inv premise`; needs [inv]. */
  private val reversed: Set<CallableDefinition> = emptySet(),
  /** `Paths.inv`. */
  private val inv: ArendRef? = null,
  /** Implicit parameters given by name in every application, as the eliminated parameters of a recursive call (`id/=suc {n} q`): what the typechecker would infer may not pass the termination check as written. */
  private val fixedImplicits: Map<String, ConcreteExpression> = emptyMap(),
): ProofStepGenerator<ArendGoal> {
  companion object {
    const val CLOSING_FACTOR = 0.25
    /** Equation-to-equation lemmas stacked with a hole below, beyond which no more are applied. */
    const val MAX_EQUATION_TOWER = 2
    const val SUBGOAL_COST = 0.25
    /** Added when an implicit argument the typechecker cannot infer is given a subterm of the goal. */
    const val GIVEN_ARGUMENT_COST = 0.3
    /** At most this many subterms of the goal are tried for such an argument. */
    const val MAX_GIVEN_ARGUMENTS = 8
    /** At most this many premises are tried as the first argument of a transitivity-like premise. */
    const val MAX_NESTED_PREMISES = 12
    /** Added for a premise applied inside the argument of another, as `<=-transitive (<=_* ...) {?}`. */
    const val NESTED_COST = 0.4
    /** At most this many hypotheses are tried as an argument of one application. */
    const val MAX_HYPOTHESIS_ARGUMENTS = 4

    /** The number of explicit arguments a term of type [expression] takes. */
    fun arity(expression: Expression): Int {
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

    /**
     * How many subgoals applying [def] to a goal of arity [goalArity] opens: its explicit arguments
     * that cannot be inferred from the result; null if [def] cannot be applied to such a goal.
     */
    fun subgoalCount(def: CallableDefinition, goalArity: Int): Int? {
      val signature = signature(def) ?: return null
      val numArgsToAdd = arity(signature) - goalArity
      if (numArgsToAdd < 0) return null
      return subgoals(signature, numArgsToAdd).count { it }
    }

    /** The parameters a premise is applied to, in order, and the type of the application. */
    private class Signature(val params: List<DependentLink>, val resultType: Expression?)

    private fun arity(signature: Signature): Int =
      signature.params.count { it.isExplicit } + (signature.resultType?.let(::arity) ?: 0)

    /**
     * For each of the first [numArgsToAdd] explicit parameters, whether it becomes a subgoal: an
     * argument that the types of later parameters or the result mention is inferred from the
     * expected type, any other has to be constructed.
     */
    private fun subgoals(signature: Signature, numArgsToAdd: Int): List<Boolean> {
      val params = signature.params
      return params.withIndex().filter { it.value.isExplicit }.take(numArgsToAdd).map { (i, param) ->
        params.drop(i + 1).none { StepBuilder.occurs(param, it.type) } &&
          (signature.resultType == null || !StepBuilder.occurs(param, signature.resultType))
      }
    }

    private fun signature(def: CallableDefinition): Signature? = when (def) {
    // A result type that is a function type once unfolded, `n /= suc n` as `n = suc n -> Empty`, takes arguments too
    is FunctionDefinition -> {
      val params = DependentLink.Helper.toList(def.parameters).toMutableList()
      var type: Expression? = def.resultType
      // Weak head normalization, as [arity] of the goal: a `\type` such as an order's `<=` stays folded on both sides
      while (type != null) {
        val pi = type.normalize(NormalizationMode.WHNF) as? PiExpression ?: break
        params += DependentLink.Helper.toList(pi.parameters)
        type = pi.codomain
      }
      Signature(params, type)
    }
    is Constructor -> Signature(DependentLink.Helper.toList(def.parameters), null)
    // A field's type is `\Pi (this : C) -> T`; the instance is inferred, the arguments are those of T
    is ClassField -> {
      val params = mutableListOf<DependentLink>()
      var type: Expression = def.type.codomain
      while (type is PiExpression) {
        params += DependentLink.Helper.toList(type.parameters)
        type = type.codomain
      }
      Signature(params, type)
    }
    else -> null
  }
  }

  /**
   * The implicit parameters of [signature] that nothing determines once the explicit arguments are
   * holes: those the result type does not mention, such as `y` of `<=-transitive {x y z} : x <= y -> y <= z -> x <= z`.
   */
  private fun uninferable(signature: Signature): List<DependentLink> {
    val resultType = signature.resultType ?: return emptyList()
    return signature.params.filter { !it.isExplicit && !StepBuilder.occurs(it, resultType) }
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    val expectedArity = arity(goal.expectedType)
    val context = StepBuilder.context(goal)
    // Lemmas turning one equation into another (`just-injective`, `inv`, `pmap f`) are not stacked more than two
    // deep with a hole below: `just-injective (pmap just (just-injective {?}))` towers lead nowhere, and nobody
    // writes them; a closing application (`pmap pred p`) is fine at any depth
    val equationTower = enclosingEquationTower(goal, currentProof)
    val goalSubterms by lazy {
      // Normalized too: the middle term `Big x l` of `a ∧ Big x l <= x` only shows once `Big x (a :: l)` computes
      (ConclusionMatcher.subterms(goal.expectedType) + ConclusionMatcher.subterms(goal.expectedType.normalize(NormalizationMode.NF)))
        // Elements only: not types, nor functions such as the partial applications of the goal's relation
        .filter { it !is LamExpression && it !is PiExpression && it !is UniverseExpression && it.type?.normalize(NormalizationMode.WHNF).let { type -> type != null && type !is UniverseExpression && type !is PiExpression } }
        .distinctBy { it.toString() }.take(MAX_GIVEN_ARGUMENTS)
    }
    return premises.flatMap { premise ->
      if (equationTower >= MAX_EQUATION_TOWER && equationToEquation(premise) && subgoalCount(premise, expectedArity) != 0) return@flatMap emptyList()
      val signature = signature(premise) ?: return@flatMap emptyList()
      val numArgsToAdd = arity(signature) - expectedArity
      if (numArgsToAdd < 0) return@flatMap emptyList()
      // `def` applied to its first explicit arguments: a hole where the argument is inferred, a subgoal otherwise
      val subgoals = subgoals(signature, numArgsToAdd)
      val explicitParams = signature.params.filter { it.isExplicit }.take(numArgsToAdd)
      val premiseCost = premiseCosts[premise] ?: 1.0
      val backwards = premise in reversed
      fun tryBuild(arguments: List<ConcreteExpression>, opened: Int, given: Pair<DependentLink, ConcreteExpression>? = null): StepBuilder.Outcome {
        val application = if (given == null && fixedImplicits.isEmpty()) {
          factory.app(factory.ref(premise.ref), arguments.map { factory.arg(it, true) })
        } else {
          // Every parameter in order, so that the given implicit argument lands on its parameter; a field's instance comes first
          val explicit = ArrayDeque(arguments)
          val all = (if (premise is ClassField) listOf(null) else emptyList()) + signature.params
          factory.app(factory.ref(premise.ref), all.mapNotNull { param ->
            when {
              // A field's instance slot takes the fixed `this` too (`cancel_*-left {toGroup A} x p`)
              param == null -> factory.arg(fixedImplicits["this"] ?: factory.hole(), false)
              given != null && param == given.first -> factory.arg(given.second, false)
              !param.isExplicit -> factory.arg(fixedImplicits[param.name] ?: factory.hole(), false)
              else -> explicit.removeFirstOrNull()?.let { factory.arg(it, true) }
            }
          })
        }
        val term = if (backwards) factory.app(factory.ref(inv ?: return StepBuilder.Outcome(null, StepBuilder.Failure.OTHER)), true, application) else application
        val cost = (if (opened == 0) premiseCost * CLOSING_FACTOR else premiseCost + opened * SUBGOAL_COST) + (if (given != null) GIVEN_ARGUMENT_COST else 0.0)
        return StepBuilder.tryBuild(goal, currentProof, term, cost, moduleLocation, accept)
      }
      fun build(arguments: List<ConcreteExpression>, opened: Int, given: Pair<DependentLink, ConcreteExpression>? = null): ProofStep<ArendGoal>? =
        tryBuild(arguments, opened, given).step
      val plain = subgoals.map { if (it) factory.goal() else factory.hole() }
      val steps = mutableListOf<ProofStep<ArendGoal>>()
      val plainOutcome = tryBuild(plain, subgoals.count { it })
      val plainStep = plainOutcome.step?.also { steps.add(it) }
      // A premise whose plain application does not even fit by shape gets no variants: an argument
      // given differently cannot mend a mismatched conclusion, and each variant is a typecheck
      if (plainStep == null && !plainOutcome.onlyInference) return@flatMap steps
      // An implicit argument the typechecker cannot infer, as the middle term of a transitivity, is
      // given a subterm of the goal: `<=-transitive {_} {_} {Big x l} {?} {?}`; or the first argument
      // is a premise applied, which fixes the middle term: `<=-transitive (<=_*_positive-right {?} {?}) {?}`
      if (plainStep == null) {
        uninferable(signature).singleOrNull()?.let { param ->
          if (System.getProperty("proofsearch.debug") == "true") println("Given arguments for ${premise.ref.refName}.${param.name} at ${goal.expectedType}: ${goalSubterms.map { it.toString() }}")
          for (subterm in goalSubterms) {
            val concrete = CoreToConcrete.convert(subterm, goal) ?: continue
            build(plain, subgoals.count { it }, param to concrete)?.let { steps.add(it) }
          }
          val first = subgoals.indexOf(true)
          val goalLeft = ConclusionMatcher.relationSides(goal.expectedType)?.first
          if (first >= 0 && goalLeft != null) {
            val firstHead = PremiseRetriever.head(explicitParams[first].type)
            // The inner premise concludes `l R m` for the goal `l R r`: its left side must match the goal's
            val nested = premises.mapNotNull { inner ->
              if (inner == premise) return@mapNotNull null
              val conclusion = ConclusionMatcher.conclusion(inner) ?: return@mapNotNull null
              if (firstHead != null && PremiseRetriever.head(conclusion) != firstHead) return@mapNotNull null
              val innerLeft = ConclusionMatcher.relationSides(conclusion)?.first ?: return@mapNotNull null
              val fit = ConclusionMatcher.match(innerLeft, goalLeft) ?: return@mapNotNull null
              inner to fit
            }.sortedWith(compareBy({ -it.second }, { premiseCosts[it.first] ?: 1.0 })).take(MAX_NESTED_PREMISES).map { it.first }
            for (inner in nested) {
              val innerSignature = signature(inner) ?: continue
              val innerSubgoals = subgoals(innerSignature, innerSignature.params.count { it.isExplicit })
              val innerTerm = factory.app(factory.ref(inner.ref), innerSubgoals.map { factory.arg(if (it) factory.goal() else factory.hole(), true) })
              val arguments = plain.toMutableList().also { it[first] = innerTerm }
              val innerCost = (premiseCosts[inner] ?: 1.0) * CLOSING_FACTOR + NESTED_COST
              StepBuilder.build(goal, currentProof, factory.app(factory.ref(premise.ref), arguments.map { factory.arg(it, true) }), premiseCost + (subgoals.count { it } - 1 + innerSubgoals.count { it }) * SUBGOAL_COST + innerCost, moduleLocation, accept)?.let { steps.add(it) }
            }
          }
        }
      }
      // A hypothesis as one of the subgoal arguments, when its type is headed like the parameter's
      var tried = 0
      // A function-typed parameter, as `p : \Pi (a : A) -> P a` of `all-forall`, takes any function-typed hypothesis
      fun kind(type: Expression): Any? = PremiseRetriever.head(type) ?: if (StepBuilder.unfold(type) is PiExpression) PiExpression::class else null
      for ((i, isSubgoal) in subgoals.withIndex()) {
        if (!isSubgoal) continue
        val paramHead = kind(explicitParams[i].type) ?: continue
        for ((ref, binding) in context) {
          if (tried >= MAX_HYPOTHESIS_ARGUMENTS) break
          val hypothesisType = StepBuilder.unfold(binding.type)
          // A hypothesis concluding the parameter's kind: itself, or applied to holes when it is a function
          // of the right conclusion, as `mon _` for `mon : \Pi (n : Nat) -> suc (f n) <= f (suc n)`
          val argument = when {
            hypothesisType is PiExpression && paramHead != PiExpression::class ->
              if (PremiseRetriever.head(hypothesisType) == paramHead) factory.app(factory.ref(ref), true, List(arity(hypothesisType)) { factory.hole() }) else continue
            kind(binding.type) == paramHead -> factory.ref(ref)
            else -> continue
          }
          tried++
          val arguments = plain.toMutableList().also { it[i] = argument }
          build(arguments, subgoals.count { it } - 1)?.let { steps.add(it) }
        }
      }
      steps
    }
  }

  /** Whether [premise] concludes an equation from its last explicit parameter, an equation, the others not being equations (`inv`, `pmap f`, `just-injective`). */
  private fun equationToEquation(premise: CallableDefinition): Boolean {
    val signature = signature(premise) ?: return false
    val explicit = signature.params.filter { it.isExplicit }
    val last = explicit.lastOrNull() ?: return false
    return RewriteGenerator.equationSides(signature.resultType ?: return false) != null && RewriteGenerator.equationSides(last.type) != null &&
      explicit.dropLast(1).none { RewriteGenerator.equationSides(it.type) != null }
  }

  /** How many applications of equation-to-equation lemmas ([equationToEquation]) directly enclose the goal, innermost first, one inside the other. */
  private fun enclosingEquationTower(goal: ArendGoal, currentProof: Proof<ArendGoal>?): Int {
    val proof = currentProof as? ArendProof ?: return 0
    val target = proof.getGoals()[goal] ?: return 0
    val byName = premises.associateBy { it.ref.refName }
    /** The tower height above the target inside [expr], or null if the target is not in it; -1 once something else intervenes. */
    fun tower(expr: org.arend.term.concrete.Concrete.Expression?): Int? {
      if (expr == null) return null
      if (expr === target) return 0
      return when (expr) {
        is org.arend.term.concrete.Concrete.AppExpression -> {
          for (argument in expr.arguments) {
            val inner = tower(argument.expression) ?: continue
            val name = (expr.function as? org.arend.term.concrete.Concrete.ReferenceExpression)?.referent?.refName
            val premise = name?.let { byName[it] }
            return if (inner >= 0 && premise != null && equationToEquation(premise)) inner + 1 else -1
          }
          tower(expr.function)?.let { -1 }
        }
        is org.arend.term.concrete.Concrete.CaseExpression -> if (expr.clauses.any { tower(it.expression) != null } || expr.arguments.any { tower(it.expression) != null }) -1 else null
        is org.arend.term.concrete.Concrete.LamExpression -> tower(expr.body)?.let { -1 }
        is org.arend.term.concrete.Concrete.TupleExpression -> if (expr.fields.any { tower(it) != null }) -1 else null
        else -> null
      }
    }
    return maxOf(0, tower(proof.getProof()) ?: 0)
  }
}
