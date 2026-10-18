package typechecker.coreapi

import org.arend.core.context.binding.Binding
import org.arend.core.expr.Expression
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.ext.error.ErrorReporter
import org.arend.ext.error.GeneralError
import org.arend.ext.error.ListErrorReporter
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.SubstConcreteVisitor
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.typechecking.error.local.GoalError
import org.arend.ext.module.LongName
import org.arend.naming.reference.LocalReferable
import org.arend.naming.reference.LocatedReferable
import org.arend.naming.reference.Referable
import org.arend.naming.scope.Scope
import java.util.TreeSet
import java.util.Collections
import java.util.IdentityHashMap
import typechecker.Proof
import typechecker.coreapi.proofstep.StepBuilder

open class ArendProof(
  private val theorem: Concrete.FunctionDefinition,
  private val goal: ArendGoal,
  /** The goals of the proof's body, when its builder has typechecked it already; otherwise they are found here. */
  goals: Map<ArendGoal, Concrete.Expression>? = null
): Proof<ArendGoal> {
  private val goalExpressions: Map<ArendGoal, Concrete.Expression>

  /** Whether the body typechecks. A proof that does not has no goals, but is not finished either. */
  val isValid: Boolean

  init {
    val found = goals ?: getProof()?.let { findGoals(it, goal) }
    isValid = found != null
    goalExpressions = found ?: emptyMap()
  }

  fun getGoals(): Map<ArendGoal, Concrete.Expression> = goalExpressions

  override fun isFinished(): Boolean = isValid && goalExpressions.isEmpty()

  fun getProof(): Concrete.Expression? = theorem.body.term

  /** A pattern as source: concrete patterns print no source themselves. */
  private fun patternSource(pattern: Concrete.Pattern, nested: Boolean = false): String = when (pattern) {
    is Concrete.NamePattern -> pattern.referable?.refName ?: "_"
    is Concrete.NumberPattern -> pattern.number.toString()
    is Concrete.TuplePattern -> if (pattern.patterns.isEmpty()) "()" else pattern.patterns.joinToString(", ", "(", ")") { patternSource(it) }
    is Concrete.ConstructorPattern -> {
      val name = (pattern.constructor as? org.arend.naming.reference.Referable)?.refName ?: pattern.constructor.toString()
      val text = (listOf(name) + pattern.patterns.map { patternSource(it, nested = true) }).joinToString(" ")
      if (nested && pattern.patterns.isNotEmpty()) "($text)" else text
    }
    else -> pattern.toString()
  }

  /**
   * The body as Arend source after the signature: `=> term`, or, when the term is a chain of
   * `\case \elim` on parameters, `\elim x, y` and clauses, which is what Arend's termination
   * checker needs to accept a recursive call (it does not look through `\case`).
   */
  fun toSource(): String {
    val term = getProof() ?: return "=> {?}"
    return toSource(term)
  }

  /**
   * [toSource] with each global name written as briefly as [scope], the module the proof lives in,
   * allows: the plain name when it resolves there to the definition used, else the name qualified
   * by its class (`AddGroup.negative-isInv`), else by its module (`Arith.Nat.-'=0`, needed when the
   * module defines a lemma of the same name itself); the modules of the names written that way are
   * returned, for the file to import. Without a scope every name is written in full.
   */
  fun qualifiedSource(scope: Scope? = null): Pair<String, Set<String>> {
    val term = getProof() ?: return "=> {?}" to emptySet()
    val modules = TreeSet<String>()
    fun resolvesTo(name: String, referent: Referable): Boolean {
      if (scope == null) return false
      val resolved = Scope.resolveName(scope, LongName.fromString(name).toList()) ?: return false
      val unwrapped = (resolved as? org.arend.ext.reference.DataContainer)?.data as? Referable
      return resolved == referent || unwrapped == referent
    }
    val qualified = term.accept(object : ProofCopier() {
      override fun visitReference(expr: Concrete.ReferenceExpression, params: Void?): Concrete.Expression {
        val referent = expr.referent as? LocatedReferable ?: return super.visitReference(expr, params)
        val module = referent.location?.modulePath?.toString() ?: return super.visitReference(expr, params)
        if (module == "Prelude" || resolvesTo(referent.refName, referent)) return super.visitReference(expr, params)
        val longName = referent.refLongName.toString()
        val name = if (longName != referent.refName && resolvesTo(longName, referent)) longName else "$module.$longName".also { modules.add(module) }
        // An infix name used in prefix position is parenthesized, `(Meta.in) (rewriteI p) h`, or the parser reads it as an operator
        return Concrete.ReferenceExpression(expr.data, LocalReferable(if (referent.precedence.isInfix) "($name)" else name))
      }
    }, null)
    return toSource(qualified) to modules
  }

  private fun toSource(term: Concrete.Expression): String {
    // In declaration order, which `\elim` must follow; the theorem's own parameter list comes from a context map
    val parameters = (goal.definition as? org.arend.core.definition.FunctionDefinition)
      ?.let { org.arend.core.context.param.DependentLink.Helper.toList(it.parameters).mapNotNull { link -> link.name } }
      ?: theorem.parameters.flatMap { it.referableList }.mapNotNull { it?.refName }
    // `\elim a, l, a` cannot say which `a` it means when two parameters share a name (`allC-tail`'s element
    // and hypothesis): the nested `\case \elim` form, which refers to the innermost one, is kept then
    if (parameters.size != parameters.toSet().size) return "=> " + clausesOnly(term.toString())
    // A leading lambda, `\lam p => \case \elim n, \elim p ...` for a lemma concluding `n /= suc n`: the clauses go
    // outside it (`\elim n | suc n => \lam p => ...`), so that a recursive call is in an `\elim` clause body, where
    // Arend checks termination; a variable it binds that the cases carry along is simply left to it
    val lambda = term as? Concrete.LamExpression
    val lambdaNames = lambda?.parameters?.flatMap { param -> param.referableList.mapNotNull { it?.refName } }?.toSet() ?: emptySet()
    val columns = mutableListOf<String>()
    // A column's pattern, or null while it is still the variable itself
    class Row(val patterns: Map<String, Concrete.Pattern?>, val body: Concrete.Expression)

    /** Whether [pattern] binds [name] as a plain variable somewhere, so a later split of it refines this pattern. */
    fun binds(pattern: Concrete.Pattern?, name: String): Boolean = when (pattern) {
      null -> false
      is Concrete.NamePattern -> pattern.referable?.refName == name
      is Concrete.ConstructorPattern -> pattern.patterns.any { binds(it, name) }
      is Concrete.TuplePattern -> pattern.patterns.any { binds(it, name) }
      else -> false
    }
    /** [pattern] with the variable [name] replaced by [replacement]: `neg x'` with `x'` split into `suc x'` is `neg (suc x')`. */
    fun substitute(pattern: Concrete.Pattern, name: String, replacement: Concrete.Pattern): Concrete.Pattern = when {
      pattern is Concrete.NamePattern && pattern.referable?.refName == name -> replacement
      pattern is Concrete.ConstructorPattern -> Concrete.ConstructorPattern(pattern.data, pattern.isExplicit, pattern.constructor, pattern.patterns.map { substitute(it, name, replacement) }, pattern.asReferable)
      pattern is Concrete.TuplePattern -> Concrete.TuplePattern(pattern.data, pattern.isExplicit, pattern.patterns.map { substitute(it, name, replacement) }, pattern.asReferable)
      else -> pattern
    }
    /** The column whose pattern a split of [name] refines: the parameter itself, or the one binding it. */
    fun columnOf(name: String, patterns: Map<String, Concrete.Pattern?>): String? = when {
      name in parameters && (patterns[name] == null || !patterns.containsKey(name)) -> name
      name in parameters -> if (binds(patterns[name], name)) name else null
      else -> patterns.entries.singleOrNull { binds(it.value, name) }?.key
    }

    fun expand(patterns: Map<String, Concrete.Pattern?>, body: Concrete.Expression): List<Row> {
      val case = body as? Concrete.CaseExpression
      val eliminated = case?.arguments?.map { (it.expression as? Concrete.ReferenceExpression)?.takeIf { _ -> it.isElim }?.referent?.refName }
      // A split of parameters, or of variables bound by the patterns so far (a hypothesis carried along, a
      // variable to refine as `x` into `suc x`, a constructor argument as `x'` of `neg x'`), becomes clauses;
      // a lambda-bound variable carried along with a variable pattern of its own name is left to the lambda
      val targets = eliminated?.map { name -> name?.let { if (it in lambdaNames) it else columnOf(it, patterns) } }
      if (case == null || case.resultType != null || targets!!.any { it == null } || targets.all { it in lambdaNames }) {
        return listOf(Row(patterns, body))
      }
      val carried = eliminated.indices.filter { eliminated[it] in lambdaNames }
      if (carried.any { i -> case.clauses.any { (it.patterns[i] as? Concrete.NamePattern)?.referable?.refName != eliminated[i] } }) return listOf(Row(patterns, body))
      targets.forEachIndexed { i, target -> if (i !in carried && target !in columns) columns.add(target!!) }
      return case.clauses.flatMap { clause ->
        val withClause = patterns.toMutableMap()
        for (i in eliminated.indices) {
          if (i in carried) continue
          val name = eliminated[i]!!
          val column = targets[i]!!
          val current = withClause[column]
          withClause[column] = if (current == null) clause.patterns[i] else substitute(current, name, clause.patterns[i])
        }
        expand(withClause, clause.expression ?: return@flatMap emptyList())
      }
    }
    val rows = expand(emptyMap(), lambda?.body ?: term)
    if (columns.isEmpty()) return "=> " + clausesOnly(term.toString())
    val lambdaPrefix = if (lambdaNames.isEmpty()) "" else "\\lam " + lambdaNames.joinToString(" ") + " => "
    // Parameters are eliminated in the order they are declared
    val ordered = parameters.filter { it in columns }
    return "\\elim " + ordered.joinToString(", ") + rows.joinToString("") { row ->
      // A clause that does not split a column keeps the variable
      "\n  | " + ordered.joinToString(", ") { row.patterns[it]?.let { p -> patternSource(p) } ?: it } + " => " + lambdaPrefix + clausesOnly(row.body.toString()).replace("\n", "\n  ")
    }
  }


  /**
   * A `\case` without arguments, as the clauses given to `mcases`, is written `\with { ... }`: the
   * concrete printer writes `(\case  \with { ... })`, which the parser does not read back.
   */
  private fun clausesOnly(source: String): String {
    val marker = "(\\case  \\with {"
    var result = source
    while (true) {
      val start = result.indexOf(marker)
      if (start < 0) return result
      // The matching brace of the clauses, then the closing parenthesis of the argument
      var depth = 0
      var i = start + marker.length - 1
      while (i < result.length) {
        when (result[i]) { '{' -> depth++; '}' -> depth-- }
        if (depth == 0) break
        i++
      }
      if (i + 1 >= result.length || result[i + 1] != ')') return result
      result = result.substring(0, start) + "\\with {" + result.substring(start + marker.length, i + 1) + result.substring(i + 2)
    }
  }

  override fun toString(): String {
    return getProof().toString()
  }

  /**
   * An error reporter that collects the goals of the proof being typechecked from the goal
   * errors, each with the typechecking context at its `{?}`, and keeps the other errors.
   */
  class GoalCollector(private val goal: ArendGoal) : ErrorReporter {
    val goals = LinkedHashMap<ArendGoal, Concrete.Expression>()
    val errors = ArrayList<GeneralError>()
    // A `{?}` may be reported more than once; the first report counts
    private val seen = Collections.newSetFromMap(IdentityHashMap<Concrete.GoalExpression, Boolean>())

    override fun report(error: GeneralError) {
      errors.add(error)
      if (error is GoalError) {
        val expression = StepBuilder.goalNode(error)
        if (expression != null && seen.add(expression)) {
          val typechecker = CheckTypeVisitor.loadTypecheckingContext(error.typecheckingContext, ListErrorReporter())
          goals[ArendGoal(error.expectedType, typechecker, goal.sourceNode, goal.definition)] = expression
        }
      }
    }

    /** Whether an error other than a goal was reported. */
    fun hasErrors(): Boolean = errors.any { it.level == GeneralError.Level.ERROR }
  }

  companion object {
    /**
     * Steps checked within the whole proof: those with a meta whose success depends on more than its own goal, and those
     * binding variables (`\case`, `\lam`), whose subgoals' contexts the whole proof's typecheck names apart (`x'`, `x''`).
     */
    private val STRUCTURE_SENSITIVE = Regex("(^|[^A-Za-z0-9_'.-])(rewrite|rewriteI|rewriteF|unfold|mcases|simplify|equation|linarith|contradiction|using|usingOnly)([^A-Za-z0-9_'-]|$)|\\\\(case|lam|let|have|Pi|Sigma)\\b")
    /**
     * The goals of [proof], from the goal errors its typechecking reports: each carries the
     * typechecking context at the `{?}`. Deferred metas such as `unfold` typecheck their argument
     * on a copy of the typechecker, so a visitor's `visitGoal` would miss the goals inside them.
     */
    fun findGoals(proof: Concrete.Expression, goal: ArendGoal): Map<ArendGoal, Concrete.Expression>? {
      val collector = GoalCollector(goal)
      val typechecker = CheckTypeVisitor.loadTypecheckingContext(goal.typechecker.saveTypecheckingContext(), collector)
      val typed = try {
        StepBuilder.withDeadline { typechecker.finalize(typechecker.typecheck(proof, goal.expectedType), proof) }
      } catch (e: Exception) {
        null
      }
      return if (typed == null || collector.hasErrors()) null else collector.goals
    }


    fun extractContext(expression: Expression, context: MutableSet<Binding>) {
      val exprQueue = ArrayDeque<Expression>(listOf(expression, expression.type))
      while (exprQueue.isNotEmpty()) {
        val expr = exprQueue.removeFirst()
        val exprContext = FreeVariablesCollector.getFreeVariables(expr)
        for (binding in exprContext) {
          if (context.contains(binding)) { continue }
          context.add(binding)
          exprQueue.addLast(binding.type)
        }
      }
    }
  }

  override fun goals(): List<ArendGoal> {
    return goalExpressions.keys.toList()
  }

  /** Copies a proof tree; unlike [SubstConcreteVisitor] alone, it keeps `\elim` on `\case` arguments. */
  private open class ProofCopier : SubstConcreteVisitor(null) {
    override fun visitCase(expr: Concrete.CaseExpression, params: Void?): Concrete.Expression {
      val copy = super.visitCase(expr, params) as Concrete.CaseExpression
      val arguments = copy.arguments.zip(expr.arguments) { arg, original ->
        Concrete.CaseArgument(arg.expression, arg.referable, arg.type, original.isElim, arg.variance)
      }
      return Concrete.CaseExpression(copy.data, copy.isSCase, arguments, copy.resultType, copy.resultTypeLevel, copy.clauses)
    }
  }

  override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): ArendProof? {
    val proofArd = proof as? ArendProof ?: return null
    val goalExpr = goalExpressions[goal] ?: return null

    // Where each `{?}` ends up in the copied tree: the proof's remaining goals and the step's own keep their goal objects
    val copies = java.util.IdentityHashMap<Concrete.Expression, Concrete.Expression>()
    val substVisitor = object : ProofCopier() {
      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression = super.visitGoal(expr, params).also { copies[expr] = it }
    }
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
    val substitutedProof = proofArd.getProof()?.accept(substVisitor, null) ?: return null

    // Copies the tree: other proof states in the search share this proof's expressions
    val newProof = getProof()?.accept(object: ProofCopier() {
      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression {
        if (expr == goalExpr) {
          return substitutedProof
        }
        return super.visitGoal(expr, params).also { copies[expr] = it }
      }
    }, null) ?: return null
    val newTheorem = goal.typechecker.factory.function(theorem.ref, theorem.kind, theorem.parameters, theorem.resultType, theorem.resultTypeLevel, goal.typechecker.factory.body(newProof)) as? Concrete.FunctionDefinition ?: return null

    // The remaining goals of this proof and the step's goals, with their `{?}` nodes in the new tree
    val merged = LinkedHashMap<ArendGoal, Concrete.Expression>()
    for ((g, node) in goalExpressions) if (g != goal) merged[g] = copies[node] ?: return null
    for ((g, node) in proofArd.goalExpressions) merged[g] = copies[node] ?: return null

    // The whole proof has to typecheck against the original goal as a unit: a step typechecked alone against its goal
    // can still fail in place, when a meta in it (`rewrite`, `unfold`, `equation`) runs before the surrounding term has
    // fixed what it needs; its remaining goals are not errors
    // Tried on 2026-10-19: plugging meta-free, binder-free steps in without this check (`merged` as the goals) lost
    // `id<isuc`, `ldistr<=` and `Dec_||` in the benchmark for a quarter of the time; every step is checked
    if (merged.isEmpty() && false) return ArendProof(newTheorem, this.goal, merged)
    val collector = GoalCollector(this.goal)
    val typechecker = CheckTypeVisitor.loadTypecheckingContext(this.goal.typechecker.saveTypecheckingContext(), collector)
    val typed = try { StepBuilder.withDeadline { typechecker.finalize(typechecker.typecheck(newProof, this.goal.expectedType), newProof) } } catch (e: Exception) { null }
    // A goal a meta left of its own, outside the proof's `{?}`s, could never be filled
    if (typed == null || collector.hasErrors() || StepBuilder.hasForeignGoals(collector.errors, newProof)) {
      if (System.getProperty("proofsearch.debug") == "true") println("Rejected as a whole: $newProof -- ${collector.errors.filter { it.level == org.arend.ext.error.GeneralError.Level.ERROR }.map { it.shortMessage }}")
      return null
    }
    return ArendProof(newTheorem, this.goal, collector.goals)
  }

}

/**
 * A goal type with a lambda at its head applied, `(\lam z => n mod m <= z) (m * (n div m) + n mod m)` after
 * a `transport`, reduced: the solvers and the matcher look at the head of the type.
 */
fun betaReduced(type: org.arend.core.expr.Expression): org.arend.core.expr.Expression {
  // Solved inference variables (the `a'` and the lemma's arguments of a transport) are replaced by their solutions:
  // the generators look for context bindings, not inference references. An unsolved one would be stripped to an
  // error term, so the type is then kept as it is
  var unsolved = false
  type.accept(object : org.arend.core.expr.visitor.VoidExpressionVisitor<Void?>() {
    override fun visitInferenceReference(expr: org.arend.core.expr.InferenceReferenceExpression, params: Void?): Void? {
      if (expr.substExpression == null) unsolved = true else expr.substExpression.accept(this, null)
      return null
    }
  }, null)
  val stripped = if (unsolved) type else type.accept(org.arend.core.expr.visitor.StripVisitor(org.arend.error.DummyErrorReporter.INSTANCE), null)
  // An application at the head of a type is either a redex or stuck on a variable or a field, which WHNF leaves as it is
  return if (stripped is org.arend.core.expr.AppExpression) stripped.normalize(org.arend.ext.core.ops.NormalizationMode.WHNF) else stripped
}
