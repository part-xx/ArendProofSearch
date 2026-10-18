package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.Constructor
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.AppExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FieldCallExpression
import org.arend.core.expr.IntegerExpression
import org.arend.core.expr.PathTypeExpression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.ext.core.ops.CMP
import org.arend.typechecking.implicitargs.equations.DummyEquations
import org.arend.ext.core.ops.NormalizationMode
import org.arend.prelude.Prelude

/**
 * Matches what a premise concludes against a goal in core, to select premises that can apply.
 *
 * Proof search over the CLI finds candidates by a symbol, in library order; this says which of
 * them fit the goal and how specifically: the score of a match is the number of definitions it
 * matches, so that `meet-left : x ∧ y <= x` (two) ranks above `<=-refl : x <= x` (one) for
 * `x ∧ x <= x`, and lemmas that conclude something else (`n * k <= m * l`) are left out. The
 * parameters of the premise match anything; the goal is also tried unfolded, so that
 * `join-left : x <= x ∨ y` matches `x <= abs x`.
 */
object ConclusionMatcher {
  private const val MAX_DEPTH = 8

  /** What a premise concludes, with its free variables and, for an equation, its sides: fixed per definition, used for thousands of goals. */
  private class Conclusion(val expression: Expression, val vars: Set<Binding>, val sides: Pair<Expression, Expression>?)
  private val conclusions = java.util.Collections.synchronizedMap(java.util.WeakHashMap<CallableDefinition, java.util.Optional<Conclusion>>())

  private fun conclusionOf(premise: CallableDefinition): Conclusion? = conclusions.getOrPut(premise) {
    java.util.Optional.ofNullable(conclusion(premise)?.let { Conclusion(it, FreeVariablesCollector.getFreeVariables(it), RewriteGenerator.equationSides(it)) })
  }.orElse(null)

  /** An expression by identity, for memoizing its normal form. */
  private class Identity(val expression: Expression) {
    override fun equals(other: Any?): Boolean = other is Identity && other.expression === expression
    override fun hashCode(): Int = System.identityHashCode(expression)
  }
  private const val WHNF_MEMO_SIZE = 50000
  /**
   * Weak head normal forms by identity, most recently used last: the same goal subterms are matched
   * against thousands of premises, and the same premise conclusions against every goal.
   */
  private val whnfMemo = object : LinkedHashMap<Identity, Expression>(1024, 0.75f, true) {
    override fun removeEldestEntry(eldest: MutableMap.MutableEntry<Identity, Expression>?): Boolean = size > WHNF_MEMO_SIZE
  }
  private fun whnf(expression: Expression): Expression = synchronized(whnfMemo) {
    whnfMemo.getOrPut(Identity(expression)) {
      // A library lemma's side may not have a normal form the evaluator can reach: it is matched as stated then
      try { expression.normalize(NormalizationMode.WHNF) } catch (e: StackOverflowError) { expression }
    }
  }

  /** The type a premise concludes, after all its parameters, which are its free variables. */
  fun conclusion(premise: CallableDefinition): Expression? {
    val type = when (premise) {
      is FunctionDefinition -> premise.resultType
      is Constructor -> premise.getDataTypeExpression(premise.makeIdLevels())
      is ClassField -> premise.type.codomain
      else -> null
    } ?: return null
    return stripPi(type)
  }

  private fun stripPi(type: Expression): Expression {
    var result = type
    while (true) {
      result = (result.normalize(NormalizationMode.WHNF) as? PiExpression)?.codomain ?: return result
    }
  }

  /** How specifically [premise] concludes [goal]; null if it cannot. A premise whose conclusion is unknown fits with 0. */
  fun applyScore(premise: CallableDefinition, goal: Expression): Int? = applyScore(premise, goal, stripPi(goal))

  /** [applyScore] with the goal's conclusion [strippedGoal] computed once for many premises. */
  fun applyScore(premise: CallableDefinition, goal: Expression, strippedGoal: Expression): Int? {
    val conclusion = conclusionOf(premise) ?: return 0
    return score(conclusion.expression, strippedGoal, conclusion.vars, 0)
  }

  /** The goal's conclusion, after its parameters: computed once per goal and passed to [applyScore]. */
  fun strippedGoal(goal: Expression): Expression = stripPi(goal)

  /**
   * The definitions at the heads of the goal's subterms, as stated, normalized, and with its sides
   * unfolded: everything a rigid head of a premise's conclusion can be matched with by [score].
   * Computed once per goal for [mayFit].
   */
  fun goalHeads(goal: Expression): Set<Any> {
    val stripped = stripPi(goal)
    val sides = RewriteGenerator.equationSides(stripped)?.toList() ?: listOf(stripped)
    return (subterms(stripped) + subterms(stripped.normalize(NormalizationMode.NF)) + sides.map { whnf(it) })
      .mapNotNull { SubtermIndex.headKey(it) }.toSet()
  }

  /**
   * Whether [premise] may conclude a goal with [goalHeads], a necessary condition for [applyScore] and
   * [reversedApplyScore] to succeed: the head of each side of its conclusion, if it is a definition
   * rather than a parameter, as stated or unfolded, is among the goal's heads. Thousands of
   * equations are retrieved for a goal; the few about its functions are worth matching.
   */
  fun mayFit(premise: CallableDefinition, goalHeads: Set<Any>): Boolean {
    val conclusion = conclusionOf(premise) ?: return true
    val sides = conclusion.sides?.toList() ?: listOf(conclusion.expression)
    return sides.all { side ->
      val head = rigidHead(side, conclusion.vars)
      val unfoldedHead = rigidHead(whnf(side), conclusion.vars)
      head == null || unfoldedHead == null || head in goalHeads || unfoldedHead in goalHeads
    }
  }

  /** The definition at the head of [expr] that a match must find in the goal; null when anything may match: a parameter, a field of a parameter instance, a type former. */
  private fun rigidHead(expr: Expression, vars: Set<Binding>): Any? {
    var current = expr
    while (current is AppExpression) current = current.function
    return when (current) {
      is FieldCallExpression -> if (current.argument is ReferenceExpression && (current.argument as ReferenceExpression).binding in vars) null else current.definition
      is IntegerExpression -> if (current.isZero) Prelude.ZERO else Prelude.SUC
      is DefCallExpression -> current.definition
      else -> null
    }
  }

  /**
   * How specifically the equation [premise] concludes matches [goal] read backwards, for applying
   * `inv premise`: `ide-right : x * ide = x` to `pow a n = pow a n * ide`. Null if it does not, or
   * if either is not an equation.
   */
  fun reversedApplyScore(premise: CallableDefinition, goal: Expression): Int? {
    val conclusion = conclusionOf(premise) ?: return null
    val (left, right) = conclusion.sides ?: return null
    val (goalLeft, goalRight) = RewriteGenerator.equationSides(stripPi(goal)) ?: return null
    val vars = conclusion.vars
    return (score(left, goalRight, vars, 1) ?: return null) + (score(right, goalLeft, vars, 1) ?: return null) + 1
  }

  /**
   * How specifically a side of the equation [premise] concludes occurs in [goal], for rewriting
   * with it; null if neither side does. A side that is a bare parameter does not count: the
   * rewrite meta would match anything with it.
   */
  fun rewriteScore(premise: CallableDefinition, goal: Expression, subterms: List<Expression> = goalSubterms(goal)): Int? {
    val (left, right) = rewriteSideScores(premise, goal, subterms) ?: return null
    return listOfNotNull(left, right).maxOrNull()
  }

  /**
   * For each side of the equation [premise] concludes, how specifically it occurs in [goal]: the
   * left score says whether `rewrite premise` applies, the right one whether `rewriteI premise`
   * does. A bare parameter as a side gets null: it would match anything. Null if [premise] is not
   * an equation.
   */
  fun rewriteSideScores(premise: CallableDefinition, goal: Expression, subterms: List<Expression> = goalSubterms(goal)): Pair<Int?, Int?>? =
    rewriteSideScores(premise, SubtermIndex(subterms))

  /** [rewriteSideScores] against the goal's subterms indexed by head once, for many premises. */
  fun rewriteSideScores(premise: CallableDefinition, index: SubtermIndex): Pair<Int?, Int?>? {
    val (left, right) = RewriteGenerator.lemmaSides(premise) ?: return null
    fun sideScore(side: Expression): Int? {
      if (side is ReferenceExpression) return null
      val vars = FreeVariablesCollector.getFreeVariables(side)
      return index.candidates(side).mapNotNull { score(side, it, vars, 0) }.filter { it > 0 }.maxOrNull()
    }
    return sideScore(left) to sideScore(right)
  }

  /**
   * The subterms of a goal grouped by the definition at their head: a lemma side headed by `*` can
   * only match a subterm headed by `*`, so the thousand equations retrieved for a goal are each
   * compared with a few subterms rather than all of them.
   */
  class SubtermIndex(subterms: List<Expression>) {
    private val byHead: Map<Any?, List<Expression>> = subterms.groupBy { headKey(it) }
    private val all: List<Expression> = subterms

    /** The subterms [side] may match: those with its head, or all of them when its head is a variable. */
    fun candidates(side: Expression): List<Expression> {
      val key = headKey(side) ?: return all
      return byHead[key].orEmpty()
    }

    companion object {
      /** The definition at the head of an application, a numeral's constructor, or null for a variable head. */
      fun headKey(expr: Expression): Any? {
        var current = expr
        while (current is AppExpression) current = current.function
        return when (current) {
          is IntegerExpression -> if (current.isZero) Prelude.ZERO else Prelude.SUC
          is DefCallExpression -> current.definition
          is PathTypeExpression -> Prelude.PATH
          else -> null
        }
      }
    }
  }

  /** The two sides of a binary relation `a R b`, an equation or the last two arguments of the head; null otherwise. */
  fun relationSides(type: Expression): Pair<Expression, Expression>? {
    RewriteGenerator.equationSides(type)?.let { return it }
    val args = arguments(stripPi(type)) ?: return null
    return if (args.size >= 2) args[args.size - 2] to args[args.size - 1] else null
  }

  /** How specifically [pattern], whose free variables match anything, matches [target]; null if it does not, and null for a bare variable. */
  fun match(pattern: Expression, target: Expression): Int? {
    if (pattern is ReferenceExpression) return null
    return score(pattern, target, FreeVariablesCollector.getFreeVariables(pattern), 0)
  }

  /** [match] with the given [vars] as the pattern's variables: a context variable in the pattern (`f` in `f (suc n)`) is then rigid. */
  fun match(pattern: Expression, target: Expression, vars: Set<Binding>): Int? {
    if (pattern is ReferenceExpression) return null
    return score(pattern, target, vars, 0)
  }

  /** The subterms of [goal], as it is and normalized: `a ∧ Big x l` only shows once `Big x (a :: l)` computes. */
  fun goalSubterms(goal: Expression): List<Expression> = subterms(goal) + subterms(goal.normalize(NormalizationMode.NF))

  /** Whether [expr] occurs in [goal], as a subterm of it or of its normal form. */
  fun occursIn(expr: Expression, goal: Expression): Boolean {
    if (expr is ReferenceExpression) return StepBuilder.occurs(expr.binding, goal)
    return goalSubterms(goal).any { CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, expr, it, null, null) }
  }

  /** The subterms of [expr] down to a bounded depth, [expr] first, through applications, equations, fields and calls. */
  fun subterms(expr: Expression): List<Expression> {
    val result = mutableListOf<Expression>()
    fun visit(e: Expression, depth: Int) {
      if (depth > MAX_DEPTH) return
      result.add(e)
      when (e) {
        is AppExpression -> { visit(e.function, depth + 1); visit(e.argument, depth + 1) }
        is PathTypeExpression -> { visit(e.leftArgument, depth + 1); visit(e.rightArgument, depth + 1) }
        is FieldCallExpression -> visit(e.argument, depth + 1)
        is DefCallExpression -> e.defCallArguments.forEach { visit(it, depth + 1) }
        else -> {}
      }
    }
    visit(expr, 0)
    return result
  }

  /** `f this a1 ... an` for a field `f`: the field call, its instance, and the arguments. */
  private fun fieldApplication(expr: Expression): Triple<FieldCallExpression, Expression, List<Expression>>? {
    val args = ArrayDeque<Expression>()
    var current = expr
    while (current is AppExpression) {
      args.addFirst(current.argument)
      current = current.function
    }
    return (current as? FieldCallExpression)?.let { Triple(it, it.argument, args.toList()) }
  }

  /** The arguments [expr] applies its head to, or null if it is not an application. */
  private fun arguments(expr: Expression): List<Expression>? {
    val args = ArrayDeque<Expression>()
    var current = expr
    while (current is AppExpression) {
      args.addFirst(current.argument)
      current = current.function
    }
    return when (current) {
      is DefCallExpression -> current.defCallArguments + args
      else -> if (args.isEmpty()) null else args.toList()
    }
  }

  /**
   * The number of definitions [pattern] matches in [target], where [vars] match anything;
   * null if they differ. Expressions this does not look into match with 0.
   */
  private fun score(pattern: Expression, target: Expression, vars: Set<Binding>, depth: Int): Int? {
    if (depth > MAX_DEPTH) return 0
    if (pattern is ReferenceExpression && pattern.binding in vars) return 0
    matchHeads(pattern, target, vars, depth)?.let { return it }
    // The goal may only show the premise's form after unfolding, e.g. `x - y` as `x + negative y`;
    // or the premise is stated with a definition the goal does not use, e.g. LinearOrder's `<=`
    val unfoldedTarget = whnf(target)
    val unfoldedPattern = whnf(pattern)
    if (unfoldedTarget !== target) matchHeads(pattern, unfoldedTarget, vars, depth)?.let { return it }
    if (unfoldedPattern !== pattern) {
      matchHeads(unfoldedPattern, target, vars, depth)?.let { return it }
      if (unfoldedTarget !== target) matchHeads(unfoldedPattern, unfoldedTarget, vars, depth)?.let { return it }
    }
    return null
  }

  private fun matchHeads(pattern: Expression, target: Expression, vars: Set<Binding>, depth: Int): Int? {
    fun sum(pairs: List<Pair<Expression, Expression>>, own: Int): Int? {
      var total = own
      for ((p, t) in pairs) total += score(p, t, vars, depth + 1) ?: return null
      return total
    }
    // An equation is written `a = b`, a call of the infix `=`, and also appears as `Path` or as a path type: by their sides.
    // Below the top level as written only: normalizing every subterm to look for an equation was most of a fit's cost
    val patternSides = if (depth == 0) RewriteGenerator.equationSides(pattern) else RewriteGenerator.equationSidesAsWritten(pattern)
    val targetSides = if (depth == 0) RewriteGenerator.equationSides(target) else RewriteGenerator.equationSidesAsWritten(target)
    if (patternSides != null && targetSides != null) return sum(listOf(patternSides.first to targetSides.first, patternSides.second to targetSides.second), 1)
    if ((patternSides == null) != (targetSides == null)) return null
    return when (pattern) {
      is PathTypeExpression ->
        if (target is PathTypeExpression) sum(listOf(pattern.leftArgument to target.leftArgument, pattern.rightArgument to target.rightArgument), 1) else null
      is AppExpression -> {
        // `f a` for a parameter `f`, as in `pmap : f a = f a'`, is any application at all
        val head = generateSequence<Expression>(pattern) { (it as? AppExpression)?.function }.last()
        if (head is ReferenceExpression && head.binding in vars) return if (arguments(target) != null) 0 else null
        if (target is AppExpression) {
          sum(listOf(pattern.function to target.function, pattern.argument to target.argument), 0)?.let { return it }
        }
        // A field of an unknown instance, such as `<=` in `<=-refl : x <= x`, may be implemented by
        // any definition, such as Nat's `<=`: only the arguments can be compared
        val (field, instance, args) = fieldApplication(pattern) ?: return null
        if (instance !is ReferenceExpression || instance.binding !in vars) return null
        val targetArgs = arguments(target) ?: return null
        if (targetArgs.size < args.size || field.definition == (target as? DefCallExpression)?.definition) return null
        sum(args.zip(targetArgs.takeLast(args.size)), 1)
      }
      is FieldCallExpression ->
        if (target is FieldCallExpression && target.definition == pattern.definition) sum(listOf(pattern.argument to target.argument), 1) else null
      is DefCallExpression -> {
        // Numerals are `zero` and `suc` applications in disguise
        if (target is IntegerExpression && pattern.definition == Prelude.ZERO) return if (target.isZero) 1 else null
        if (target is IntegerExpression && pattern.definition == Prelude.SUC) {
          return if (target.isZero) null else sum(listOf(pattern.defCallArguments.last() to target.pred()), 1)
        }
        if (target !is DefCallExpression || target.definition != pattern.definition) return null
        val args = pattern.defCallArguments
        val targetArgs = target.defCallArguments
        if (args.size != targetArgs.size) 1 else sum(args.zip(targetArgs), 1)
      }
      is IntegerExpression -> if (target is IntegerExpression && pattern.isEqual(target)) 1 else null
      is ReferenceExpression -> if (target is ReferenceExpression && target.binding == pattern.binding) 1 else null
      // A projection, as `n mod m` unfolded to `(divMod n m).2`: the typechecker leaves it so in a subgoal
      is org.arend.core.expr.ProjExpression ->
        if (target is org.arend.core.expr.ProjExpression && target.field == pattern.field) sum(listOf(pattern.expression to target.expression), 1) else null
      // Lambdas, Pi and Sigma types, universes...: not looked into
      else -> 0
    }
  }
}
