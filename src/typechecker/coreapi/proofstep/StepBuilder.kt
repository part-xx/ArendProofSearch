package typechecker.coreapi.proofstep

import kotlin.math.max
import kotlin.math.min

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.expr.FunCallExpression
import org.arend.core.subst.ExprSubstitution
import org.arend.ext.core.definition.CoreFunctionDefinition
import org.arend.ext.core.ops.NormalizationMode
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.ext.concrete.definition.FunctionKind
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.error.GeneralError
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.Precedence
import org.arend.naming.reference.FullModuleReferable
import org.arend.naming.reference.LocalReferable
import org.arend.naming.reference.Referable
import org.arend.term.concrete.BaseConcreteExpressionVisitor
import org.arend.typechecking.error.local.GoalError
import java.util.Collections
import java.util.IdentityHashMap
import org.arend.term.concrete.Concrete
import org.arend.typechecking.visitor.CheckTypeVisitor
import typechecker.Proof
import typechecker.ProofStep
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof
import org.arend.core.expr.Expression

/** Turns candidate terms for a goal into proof steps. */
object StepBuilder {
  /** With `-Dproofsearch.debug=true`, rejected terms are printed with their errors. */
  private val debug = System.getProperty("proofsearch.debug") == "true"
  /** `-Dproofsearch.timing=true` prints the time each heuristic takes per goal, without the per-candidate output of [debug]. */
  val timing = debug || System.getProperty("proofsearch.timing") == "true"
  /** `-Dproofsearch.noTermMemo=true` turns the memo of rejected terms off, for bisecting a regression. */
  private val noTermMemo = System.getProperty("proofsearch.noTermMemo") == "true"
  /** `-Dproofsearch.verifyTermMemo=true` typechecks remembered rejections again and reports a term that now typechecks. */
  private val verifyTermMemo = System.getProperty("proofsearch.verifyTermMemo") == "true"

  /** When the search gives up, in absolute milliseconds: past it, no more steps are built. */
  @Volatile var deadline: Long = Long.MAX_VALUE
  const val SLOW_TYPECHECK_MILLIS = 5000
  /** A single term's typecheck is abandoned after this long. */
  const val MAX_TYPECHECK_MILLIS = 5000L
  private val typecheckExecutor: java.util.concurrent.ExecutorService = java.util.concurrent.Executors.newCachedThreadPool { runnable ->
    Thread(runnable, "step-typecheck").apply { isDaemon = true }
  }

  fun pastDeadline(): Boolean = System.currentTimeMillis() > deadline

  /** Cancels a typechecking computation once the deadline has passed: a meta solver may otherwise run for minutes. */
  private val deadlineIndicator = object : org.arend.typechecking.computation.CancellationIndicator {
    override fun isCanceled(): Boolean = pastDeadline()
    override fun cancel() {}
  }

  /**
   * Runs [computation] under the deadline; null if it was interrupted by it. Nested calls (a step's
   * proof is re-typechecked while the step is built) run inside the outer one's indicator.
   */
  fun <T> withDeadline(computation: () -> T?): T? =
    if (org.arend.typechecking.computation.ComputationRunner.isCancellationIndicatorSet()) computation()
    else org.arend.typechecking.computation.ComputationRunner<T?>().run(deadlineIndicator) { computation() }

  /**
   * Typechecks [term] against [goal] and, if it fits, returns the step that fills [goal] with it
   * in [currentProof]. The `{?}` goals inside [term] become the step's subgoals.
   */
  /** Why a term was not a step: it did not typecheck at all, or only arguments were left undetermined. */
  enum class Failure { MISMATCH, INFERENCE, OTHER }

  /** A built step, or the [failure] when the term was rejected. */
  class Outcome(val step: ProofStep<ArendGoal>?, val failure: Failure?) {
    /** The term fits by shape; only an argument the typechecker could not infer stood in the way. */
    val onlyInference: Boolean get() = failure == Failure.INFERENCE
  }

  fun build(
    goal: ArendGoal, currentProof: Proof<ArendGoal>?, term: ConcreteExpression, cost: Double, moduleLocation: ModuleLocation,
    /** A further condition on the typechecked term, e.g. that a recursive call decreases. */
    accept: ((Expression) -> Boolean)? = null,
  ): ProofStep<ArendGoal>? = tryBuild(goal, currentProof, term, cost, moduleLocation, accept).step

  /** [build], telling why the term was rejected when it was. */
  /** How many rejected terms are remembered before the memo is cleared. */
  const val REJECTED_MEMO_SIZE = 1_000_000
  /**
   * Terms rejected for a problem, by the hashes of the problem's text and the term's: the same statement over
   * the same context comes up in many proof states, and typechecking the same failing candidates again is
   * most of a generation's time. Only without an [tryBuild] acceptance condition, which may depend on the state.
   */
  private val rejected = HashMap<Long, Failure>()

  private fun memoKey(goal: ArendGoal, term: ConcreteExpression): Long? {
    val problem = goal.problemText
    // An unsolved inference variable prints the same while standing for different things
    if (problem.contains('?')) return null
    return (problem.hashCode().toLong() shl 32) or (term.toString().hashCode().toLong() and 0xffffffffL)
  }

  fun tryBuild(
    goal: ArendGoal, currentProof: Proof<ArendGoal>?, term: ConcreteExpression, cost: Double, moduleLocation: ModuleLocation,
    accept: ((Expression) -> Boolean)? = null,
  ): Outcome {
    if (pastDeadline()) return Outcome(null, Failure.OTHER)
    val memo = if (accept == null && !noTermMemo) memoKey(goal, term) else null
    if (memo != null) synchronized(rejected) { rejected[memo] }?.let { remembered ->
      if (!verifyTermMemo) return Outcome(null, remembered)
      val actual = typecheckStep(goal, currentProof, term, cost, moduleLocation, accept)
      if (actual.step != null) println("MEMO MISMATCH: $term remembered as $remembered but typechecks for ${goal.problemText}")
      return actual
    }
    val outcome = typecheckStep(goal, currentProof, term, cost, moduleLocation, accept)
    // Only a type mismatch is remembered: whether an argument can be inferred (`meet-left` against `x ∧ y <= x`) has turned
    // out to depend on the state, and an exception or an interrupted typecheck says nothing about the term
    if (memo != null && outcome.step == null && outcome.failure == Failure.MISMATCH && !pastDeadline()) synchronized(rejected) {
      if (rejected.size >= REJECTED_MEMO_SIZE) rejected.clear()
      rejected[memo] = outcome.failure
    }
    return outcome
  }

  private fun typecheckStep(
    goal: ArendGoal, currentProof: Proof<ArendGoal>?, term: ConcreteExpression, cost: Double, moduleLocation: ModuleLocation,
    accept: ((Expression) -> Boolean)?,
  ): Outcome {
    val collector = ArendProof.GoalCollector(goal)
    val branchTC = CheckTypeVisitor.loadTypecheckingContext(goal.typechecker.saveTypecheckingContext(), collector)
    val before = System.currentTimeMillis()
    // On its own thread with a hard limit: Arend checks the cancellation indicator only in some loops, and a single
    // typecheck has run for 13 minutes past the deadline (`summandDiv {?} {?}` against an `LDiv` in a quotient
    // monoid); an abandoned typecheck keeps running on its thread, the search goes on without it
    val future = typecheckExecutor.submit<org.arend.typechecking.result.TypecheckingResult?> {
      try {
        // Not under `withDeadline` here: `ComputationRunner` guards its (global) indicator with a global lock, which the
        // generation holds on the search's thread; the indicator it set is seen from here, and the time limit below
        // covers a typecheck that never polls it. Finalizing reports what typechecking alone defers, e.g. an instance
        // argument that cannot be inferred
        branchTC.finalize(branchTC.typecheck(term, goal.expectedType), term as Concrete.SourceNode)
      } catch (e: org.arend.util.ComputationInterruptedException) {
        null
      } catch (e: Exception) {
        // Metas may throw on terms they do not expect; such a term is simply not a step
        null
      }
    }
    val typed = try {
      future.get(max(1L, min(MAX_TYPECHECK_MILLIS, deadline - System.currentTimeMillis())), java.util.concurrent.TimeUnit.MILLISECONDS)
    } catch (e: java.util.concurrent.TimeoutException) {
      println("Typecheck abandoned after ${System.currentTimeMillis() - before}ms: $term : ${goal.expectedType}")
      null
    } catch (e: Exception) {
      null
    } finally {
      // A single term holding the search for seconds is what makes a lemma overrun its clock: always reported
      val millis = System.currentTimeMillis() - before
      if (millis >= SLOW_TYPECHECK_MILLIS) println("Slow typecheck (${millis}ms): $term : ${goal.expectedType}")
    }
    // The status misses some errors, e.g. a reference of the wrong type; goals are not errors
    if (typed == null || branchTC.status.hasErrors() || collector.hasErrors()) {
      val messages = collector.errors.filter { it.level == GeneralError.Level.ERROR }.map { it.shortMessage }
      if (debug) println("Rejected $term : ${goal.expectedType} -- $messages")
      val failure = when {
        messages.isEmpty() -> Failure.OTHER
        messages.all { it.startsWith("Cannot infer") } -> Failure.INFERENCE
        else -> Failure.MISMATCH
      }
      return Outcome(null, failure)
    }
    // Every goal reported must be one of the term's own `{?}`: a meta such as `simplify` may leave a
    // hole of its own, which is not in the term and so would never be filled
    if (hasForeignGoals(collector.errors, term as Concrete.Expression)) {
      if (debug) println("Rejected $term : ${goal.expectedType} -- a meta left a goal of its own")
      return Outcome(null, Failure.OTHER)
    }
    if (accept != null && !accept(typed.expression)) {
      if (debug) println("Rejected $term : ${goal.expectedType} -- not accepted")
      return Outcome(null, Failure.OTHER)
    }

    val factory = branchTC.factory
    // Keep the concrete term: its {?} arguments are the subgoals of the step
    val concreteParameters = branchTC.context.map { Concrete.NameParameter(it.value, true, LocalReferable(it.value.name)) }
    val functionRef = factory.global(FullModuleReferable(moduleLocation), "goal" + goal.hashCode(), Precedence.DEFAULT, null, null)
    val stepProof = ArendProof(
      factory.function(
        functionRef,
        FunctionKind.FUNC,
        concreteParameters,
        factory.core(goal.expectedType.computeTyped()),
        null,
        factory.body(term)
      ) as Concrete.FunctionDefinition,
      ArendGoal(goal.expectedType, branchTC, goal.sourceNode, goal.definition),
      collector.goals
    )
    // The search replaces the whole proof with the step's proof, so plug the step into the current proof
    // Failing to plug the step in depends on the proof state, not on the term: not remembered (no failure kind)
    val fullProof = if (currentProof == null) stepProof else currentProof.replaceGoal(goal, stepProof) ?: return Outcome(null, null)
    return Outcome(ProofStep(fullProof, cost), null)
  }

  /**
   * [expression] in weak head normal form, also unfolding `\\type` and `\\sfunc` definitions with an
   * expression body, which normalization leaves folded: `a <= a'` of a linear order is
   * `\\type <= ... => Not (a' < a)`, and `Not A` is `A -> Empty`.
   */
  fun unfold(expression: Expression): Expression {
    var current = expression.normalize(NormalizationMode.WHNF)
    repeat(8) {
      val call = current as? FunCallExpression ?: return current
      val definition = call.definition
      if (definition.kind != CoreFunctionDefinition.Kind.TYPE && definition.kind != CoreFunctionDefinition.Kind.SFUNC) return current
      val body = definition.actualBody as? Expression ?: return current
      val substitution = ExprSubstitution()
      DependentLink.Helper.toList(definition.parameters).zip(call.defCallArguments).forEach { (param, arg) -> substitution.add(param, arg) }
      current = body.subst(substitution, call.levels.makeSubstitution(definition)).normalize(NormalizationMode.WHNF)
    }
    return current
  }

  /** The `{?}` nodes of [term]. */
  fun goalNodes(term: Concrete.Expression): Set<Concrete.GoalExpression> {
    val nodes = Collections.newSetFromMap(IdentityHashMap<Concrete.GoalExpression, Boolean>())
    term.accept(object : BaseConcreteExpressionVisitor<Void?>() {
      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression {
        nodes.add(expr)
        return expr
      }
    }, null)
    return nodes
  }

  /** The `{?}` a goal error was reported for. */
  fun goalNode(error: GeneralError): Concrete.GoalExpression? =
    (error as? GoalError)?.goalExpression ?: (error as? GoalError)?.causeSourceNode as? Concrete.GoalExpression

  /** Whether [errors] report a goal that is not a `{?}` of [term] (a typechecker may report one of the term's several times). */
  fun hasForeignGoals(errors: List<GeneralError>, term: Concrete.Expression): Boolean {
    val own = goalNodes(term)
    return errors.any { it.level == GeneralError.Level.GOAL && goalNode(it) !in own }
  }

  /** Whether [binding] occurs in [expression]. */
  fun occurs(binding: Binding, expression: Expression): Boolean =
    binding in FreeVariablesCollector.getFreeVariables(expression)

  /**
   * The local context of [goal] in order: the referable that names each binding, and the binding.
   * Variables eliminated by an enclosing `\case \elim` stay in the typechecker's context under
   * placeholder referables that no source can mention; they are left out.
   */
  fun context(goal: ArendGoal): List<Pair<Referable, Binding>> = goal.typechecker.context.entries
    // CheckTypeVisitor.VeryFakeLocalReferable is private
    .filter { it.key.javaClass.simpleName != "VeryFakeLocalReferable" }
    .map { it.key to it.value }
}
