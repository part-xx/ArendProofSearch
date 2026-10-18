package typechecker.coreapi.proofstep

import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.Constructor
import org.arend.core.definition.DataDefinition
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.FunctionDefinition
import org.arend.core.elimtree.ElimBody
import org.arend.core.elimtree.ElimClause
import org.arend.core.pattern.Pattern
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.AppExpression
import org.arend.core.expr.CaseExpression
import org.arend.core.expr.ConCallExpression
import org.arend.core.expr.DataCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FieldCallExpression
import org.arend.core.expr.FunCallExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.IntegerExpression
import org.arend.core.expr.PathTypeExpression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.SigmaExpression
import org.arend.core.expr.UniverseExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.core.expr.visitor.VoidExpressionVisitor
import org.arend.core.subst.ExprSubstitution
import org.arend.ext.core.level.LevelSubstitution
import org.arend.ext.core.ops.CMP
import org.arend.typechecking.implicitargs.equations.DummyEquations
import org.arend.ext.concrete.ConcreteClause
import org.arend.ext.concrete.ConcreteFactory
import org.arend.ext.concrete.pattern.ConcretePattern
import org.arend.ext.concrete.expr.ConcreteCaseArgument
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.context.BindingVariance
import org.arend.ext.core.definition.CoreFunctionDefinition
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.error.GeneralError
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.naming.reference.CoreReferable
import org.arend.naming.reference.Referable
import org.arend.prelude.Prelude
import org.arend.term.concrete.BaseConcreteExpressionVisitor
import org.arend.term.concrete.Concrete
import org.arend.typechecking.visitor.CheckTypeVisitor
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof
import kotlin.math.min

/**
 * Case analysis, in the shapes arend-lib proofs use:
 *
 * - `\case \elim x, \elim h... \with { | c1 ... => {?} ... }` on a variable `x` of a data type
 *   that occurs in the goal; hypotheses whose types mention `x` are eliminated with it so that
 *   they see the constructor too (`suc_pred`, `headSorted`);
 * - `\case h \with { ... }` on a hypothesis of a non-recursive data type that does not occur in
 *   the goal, such as `A || B`, `Or`, `Dec`, `Tri`, `∃` or `\Sigma` (`#-symmetric`, `factor`);
 *   constructor arguments of `\Sigma` type are matched by tuple patterns, as in `inP (a, p)`;
 * - `\case h \with {}` on a hypothesis with no matching constructors, such as `Fin 0`, `n < 0`
 *   or `suc n = 0`; it closes the goal;
 * - `\case f x y \with { ... }` for a decision function `f` from [splitters] (`decideEq`,
 *   `trichotomy`, `totality`, ...) applied to two variables of the context (`<=_/=`, `tightness`),
 *   or to one (`\case <=-dec p` in `suc<=suc`);
 * - `\case L x... \with { ... }` for a lemma `L` from [splitLemmas], selected for the goal because it
 *   concludes a disjunction or a truncated existence about a function of the goal ([SplitRetriever]),
 *   applied to the variables of the context that fit its explicit parameters: `\case FinSum_char x`
 *   for a goal about `FinSum x` (`FinSum_zro`), `\case Big01_meet-isMin l a` (`Big_meet-isMin`).
 */
class CaseGenerator(
  private val moduleLocation: ModuleLocation,
  /** Decision functions, each with the cost of splitting on it. */
  private val splitters: List<Pair<ArendRef, Double>> = emptyList(),
  /** arend-lib's `mcases` meta; without it the goal's stuck `\case` expressions are not split. */
  private val mcases: ArendRef? = null,
  /** Lemmas selected for the goal to split on, with their costs ([SplitRetriever]). */
  private val splitLemmas: List<Pair<CallableDefinition, Double>> = emptyList(),
) : ProofStepGenerator<ArendGoal> {
  companion object {
    const val ABSURD_COST = 0.0
    const val VARIABLE_COST = 1.0
    const val HYPOTHESIS_COST = 0.5
    const val SPLITTER_COST = 1.5
    const val REVERSED_COST = 0.1
    /** Subtracted when the decision is about a function of the goal, as `dec<_<= a a'` for `Dec (a < a')`. */
    const val RELEVANT_BONUS = 0.3
    /** `mcases` on what the goal is stuck on: it is what blocks the goal from computing. */
    const val MCASES_COST = 1.2
    /** Subtracted from splitting a variable the goal is stuck on, as `x` in `isuc x`: the goal computes once it is split. */
    const val STUCK_BONUS = 0.8
    /**
     * Subtracted per clause beyond the first, up to [MAX_DISCOUNTED_CLAUSES]: the search charges every
     * open goal, and a split's clauses are each simpler than the goal split, unlike the subgoals of a
     * lemma applied; without this, every single-hole application ranks above a split.
     */
    const val CLAUSE_DISCOUNT = 0.75
    const val MAX_DISCOUNTED_CLAUSES = 3
    /** `\case e \as x, idp : e = x` on a compound expression of the goal. */
    const val COMPOUND_COST = 1.2
    /** A lemma split on takes at most this many explicit arguments, and is applied to at most [MAX_SPLIT_LEMMA_APPLICATIONS] choices of them. */
    const val MAX_SPLIT_LEMMA_ARGUMENTS = 2
    const val MAX_SPLIT_LEMMA_APPLICATIONS = 4
    /** At most this many compound expressions of a goal are split on, outermost first. */
    const val MAX_COMPOUND = 3
    /** A split with more clauses than this is not proposed. */
    const val MAX_CLAUSES = 9
    /** How many definitions deep the goal is unfolded when looking for the variable it is stuck on. */
    const val MAX_UNFOLDING_DEPTH = 4
  }

  /** Names for pattern variables, distinct from the context's and from each other. */
  private class Names(goal: ArendGoal, val eliminated: String? = null) {
    private val used = StepBuilder.context(goal).map { it.first.refName }.filter { it != eliminated }.toMutableSet()

    /** Lets [name] be reused: it is eliminated along with the variable, as the length of an array. */
    fun release(name: String) { used.remove(name) }

    /** A fresh name based on [base], or on the eliminated variable's name when there is no [base], as in `suc n`. */
    fun fresh(base: String?): String {
      val start = base?.takeIf { it.isNotEmpty() && it != "_" } ?: eliminated ?: "x"
      var name = start
      while (!used.add(name)) name += "'"
      return name
    }
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    val context = StepBuilder.context(goal)
    val goalIsProp = goal.expectedType.sortOfType?.isProp == true
    // Splitting again on what an enclosing \case already split on gives the same branches
    val alreadySplit = enclosingCaseArguments(goal, currentProof)
    // Hypotheses split in the enclosing \cases, by position in the context: splitting several hypotheses in
    // another order gives the same branches again, so each is split only after those before it in the context
    val enclosingHypothesisSplits = context.withIndex().filter { (_, entry) -> entry.first.refName in alreadySplit && !StepBuilder.occurs(entry.second, goal.expectedType) }.map { it.index }
    // A hypothesis, or a decision, is split before a lemma is applied, not inside the lemma's argument:
    // `\case d \with { | yes p => yes (byLeft p) ... }`, never `yes (\case d \with ...)`; both orders prove the same
    val underBinder = directlyUnderBinder(goal, currentProof)
    val stuckOn = stuckVariables(goal)

    for ((ref, binding) in context) {
      // `\type`s such as `TSetIm f b`, which is `∃ (a : A) (f a = b)`, only show their constructors unfolded
      val type = StepBuilder.unfold(binding.type)
      val step = when {
        isAbsurd(type) -> build(goal, currentProof, emptyCase(goal, ref), ABSURD_COST)
        ref.refName in alreadySplit -> null
        // Eliminating a proposition is only possible into a proposition
        type.sortOfType?.isProp == true && !goalIsProp -> null
        !underBinder && !StepBuilder.occurs(binding, goal.expectedType) -> null
        else -> splitBinding(goal, currentProof, context, ref, binding, type, binding in stuckOn, alreadySplit, enclosingHypothesisSplits)
      }
      step?.let { steps.add(it) }
    }

    // Decisions are taken on two elements of the same type, not on types, functions or instances
    val elements = context.filter { (_, binding) ->
      val type = binding.type.normalize(NormalizationMode.WHNF)
      type !is UniverseExpression && type !is PiExpression && type !is ClassCallExpression
    }
    for ((splitter, splitterCost) in splitters) {
      if (!underBinder) break
      // A decision on one element, such as `<=-dec p`
      for ((x, _) in elements) {
        splitOnApplication(goal, currentProof, splitter, listOf(x), goalIsProp, splitterCost, alreadySplit)?.let { steps.add(it) }
      }
      for ((i, xElement) in elements.withIndex()) {
        for ((j, yElement) in elements.withIndex()) {
          val (x, xBinding) = xElement
          val (y, yBinding) = yElement
          if (i == j || !CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, xBinding.type, yBinding.type, null, null)) continue
          // Prefer the arguments in the order they were introduced, as in `trichotomy a a'`
          val cost = splitterCost + if (i > j) REVERSED_COST else 0.0
          splitOnApplication(goal, currentProof, splitter, listOf(x, y), goalIsProp, cost, alreadySplit)?.let { steps.add(it) }
        }
      }
    }

    // A lemma selected for the goal, applied to the variables of the context that fit its explicit parameters
    if (underBinder) {
      for ((lemma, cost) in splitLemmas) {
        val parameters = explicitParameters(lemma)?.takeIf { it.size <= MAX_SPLIT_LEMMA_ARGUMENTS } ?: continue
        val choices = parameters.map { parameter -> context.filter { (_, binding) -> sameKind(parameter.type, binding.type) }.map { it.first } }
        if (choices.any { it.isEmpty() }) continue
        for (args in combinations(choices).take(MAX_SPLIT_LEMMA_APPLICATIONS)) {
          splitOnApplication(goal, currentProof, lemma.ref, args, goalIsProp, cost, alreadySplit)?.let { steps.add(it) }
        }
      }
    }

    steps += mcasesSteps(goal, currentProof)
    steps += compoundSteps(goal, currentProof, alreadySplit)
    return steps
  }

  /** The explicit parameters of a lemma or a field, in order; null for other definitions. */
  private fun explicitParameters(definition: CallableDefinition): List<DependentLink>? = when (definition) {
    is FunctionDefinition -> DependentLink.Helper.toList(definition.parameters).filter { it.isExplicit }
    is ClassField -> generateSequence(definition.type.codomain) { (it as? PiExpression)?.codomain }
      .filterIsInstance<PiExpression>().flatMap { DependentLink.Helper.toList(it.parameters) }.filter { it.isExplicit }.toList()
    else -> null
  }

  /** Whether a variable of type [actual] is of the kind a parameter of type [expected] takes: the same head, or both functions. */
  private fun sameKind(expected: Expression, actual: Expression): Boolean {
    val head = PremiseRetriever.head(expected)
    if (head != null) return PremiseRetriever.head(actual) == head
    return StepBuilder.unfold(expected) is PiExpression && StepBuilder.unfold(actual) is PiExpression
  }

  /** Every choice of one element per list, in order. */
  private fun <T> combinations(choices: List<List<T>>): Sequence<List<T>> =
    if (choices.isEmpty()) sequenceOf(emptyList()) else sequence {
      for (first in choices[0]) for (rest in combinations(choices.drop(1))) yield(listOf(first) + rest)
    }

  // ── mcases: the goal is stuck on a \case expression or a pattern-matching call ──

  /**
   * What a stuck expression matches on: the arguments that some clause matches by a pattern, with
   * their parameters. [occurrence] numbers the `\case` expressions, or the calls of [definition],
   * of the goal outermost first, the way `mcases {k}` and `mcases {(f, k)}` count them.
   */
  private class Match(val definition: FunctionDefinition?, val occurrence: Int, val params: List<DependentLink>, val args: List<Expression>, val matched: List<Int>)

  /**
   * The stuck `\case` expressions and calls of pattern-matching functions in the normalized goal,
   * outermost first. One whose matched arguments are all variables of the context is left out:
   * `\case \elim` on those variables gives the same branches.
   */
  private fun stuckMatches(goal: ArendGoal): List<Match> {
    val contextBindings = StepBuilder.context(goal).map { it.second }.toSet()
    val matches = mutableListOf<Match>()
    val occurrences = HashMap<FunctionDefinition?, Int>()
    fun add(definition: FunctionDefinition?, params: List<DependentLink>, args: List<Expression>, clauses: List<ElimClause<Pattern>>) {
      val occurrence = occurrences.merge(definition, 1, Int::plus)!!
      if (clauses.isEmpty() || params.size != args.size) return
      val matched = params.indices.filter { i -> clauses.any { it.patterns.getOrNull(i)?.binding == null } }
      if (matched.isEmpty()) return
      if (matched.all { (args[it] as? ReferenceExpression)?.binding in contextBindings }) return
      matches.add(Match(definition, occurrence, params, args, matched))
    }
    goal.expectedType.normalize(NormalizationMode.RNF).accept(object : VoidExpressionVisitor<Void?>() {
      override fun visitCase(expr: CaseExpression, params: Void?): Void? {
        add(null, DependentLink.Helper.toList(expr.parameters), expr.arguments, expr.elimBody.clauses)
        return super.visitCase(expr, params)
      }

      override fun visitFunCall(expr: FunCallExpression, params: Void?): Void? {
        val body = expr.definition.actualBody as? ElimBody
        if (body != null) add(expr.definition, DependentLink.Helper.toList(expr.definition.parameters), expr.defCallArguments, body.clauses)
        return super.visitFunCall(expr, params)
      }
    }, null)
    return matches
  }

  /**
   * The variables of the context that the goal is stuck on: the arguments, along the chain of
   * computation, that a `\case`, a pattern-matching function or an inductive family matches on
   * and that are variables. Only matched positions are followed (`pow a (n + suc m)` is stuck on
   * `m` because `pow` matches on its second argument and `+` on its second), through definitions
   * normalization leaves folded (`x <= y` as `Not (y < x)`, `<` of an instance implemented by a
   * family) and both sides of an equation or relation. Arguments of a function that does not match,
   * such as `mod`, are not: splitting a variable in them computes nothing.
   */
  private fun stuckVariables(goal: ArendGoal): Set<Binding> {
    val contextBindings = StepBuilder.context(goal).map { it.second }.toSet()
    val stuck = HashSet<Binding>()
    val debug = System.getProperty("proofsearch.debug") == "true"

    fun visit(expression: Expression, depth: Int) {
      if (depth > MAX_UNFOLDING_DEPTH) return
      // Arguments at matched positions: a variable there is what the computation waits for
      fun matched(params: List<DependentLink>, args: List<Expression>, clauses: List<ElimClause<Pattern>>) {
        if (params.size != args.size) return
        val positions = params.indices.filter { i -> clauses.any { it.patterns.getOrNull(i)?.binding == null } }
        // A decision on one variable against itself, `decideEq a a`: splitting `a` computes it only one
        // constructor deep (`decideEq (suc a) (suc a)` is stuck again); `mcases` settles it at once
        if (positions.size >= 2 && positions.map { (args[it] as? ReferenceExpression)?.binding }.let { bs -> bs.all { it != null } && bs.toSet().size == 1 }) return
        for (i in positions) {
          val arg = args[i]
          val binding = (arg as? ReferenceExpression)?.binding
          if (binding != null) { if (binding in contextBindings) stuck.add(binding) } else visit(arg, depth + 1)
        }
      }
      when (val e = expression.normalize(NormalizationMode.WHNF)) {
        is CaseExpression -> matched(DependentLink.Helper.toList(e.parameters), e.arguments, e.elimBody.clauses)
        is FunCallExpression -> {
          val body = e.definition.actualBody
          when {
            // Prelude's `l !! i` computes once the array is `a :: l` and the index a constructor: stuck on both
            e.definition == Prelude.ARRAY_INDEX -> e.defCallArguments.takeLast(2).forEach { arg ->
              (arg as? ReferenceExpression)?.binding?.let { if (it in contextBindings) stuck.add(it) } ?: visit(arg, depth + 1)
            }
            body is ElimBody -> matched(DependentLink.Helper.toList(e.definition.parameters), e.defCallArguments, body.clauses)
            // A definition normalization keeps folded: `\type`, `\sfunc`, or `=`
            body is Expression -> {
              val substitution = ExprSubstitution()
              DependentLink.Helper.toList(e.definition.parameters).zip(e.defCallArguments).forEach { (param, arg) -> substitution.add(param, arg) }
              visit(body.subst(substitution, e.levels.makeSubstitution(e.definition)), depth + 1)
            }
          }
        }
        is DataCallExpression -> {
          val patterns = e.definition.constructors.mapNotNull { it.patterns }
          if (patterns.isNotEmpty()) {
            val positions = e.defCallArguments.indices.filter { i -> patterns.any { it.getOrNull(i)?.binding == null } }
            // A family matching on several arguments, `n <= m` on both, computes only once each is a constructor:
            // with an irreducible one, `n mod m` in `n mod m <= n`, splitting the variables of the others is idle
            // (arend-lib proves such goals by transport or a lemma, not by `\elim n`)
            val variables = mutableListOf<Binding>()
            var computable = true
            for (i in positions) {
              val arg = e.defCallArguments[i]
              val binding = (arg as? ReferenceExpression)?.binding
              when {
                binding != null -> variables.add(binding)
                arg is ConCallExpression || arg is IntegerExpression -> {}
                else -> {
                  val before = stuck.size
                  visit(arg, depth + 1)
                  if (stuck.size == before) computable = false
                }
              }
            }
            if (computable) variables.forEach { if (it in contextBindings) stuck.add(it) }
          }
        }
        is PathTypeExpression -> { visit(e.leftArgument, depth + 1); visit(e.rightArgument, depth + 1) }
        is PiExpression -> { DependentLink.Helper.toList(e.parameters).forEach { visit(it.type, depth + 1) }; visit(e.codomain, depth + 1) }
        is AppExpression -> {
          // A class operation on an instance, `f n < n` for `<` of `NatSemiring`: its implementation, when it is
          // an inductive family. One implemented by a function matching on its arguments (`decideEq`) is for `mcases`
          val unfolded = StepBuilder.unfold(e)
          if (unfolded !is AppExpression && unfolded !is FunCallExpression) visit(unfolded, depth + 1)
          // A relation of an abstract instance, `l i <= Big (∨) x l` in a lattice, does not compute itself, but
          // its arguments do: the goal is stuck on `l` (`Big_<=_join1` splits it)
          else if (unfolded is AppExpression) {
            var head: Expression = unfolded
            val args = ArrayDeque<Expression>()
            while (head is AppExpression) { args.addFirst(head.argument); head = head.function }
            if (head is FieldCallExpression) {
              if (head.argument is ReferenceExpression) args.forEach { visit(it, depth + 1) }
              // A field of a concrete instance, `at {a :: l} i`: its implementation computes on the argument
              else args.forEach { arg -> (arg as? ReferenceExpression)?.binding?.let { if (it in contextBindings) stuck.add(it) } ?: visit(arg, depth + 1) }
            }
          }
        }
        else -> {}
      }
    }
    visit(goal.expectedType, 0)
    if (debug) println("Stuck variables of ${goal.expectedType}: ${stuck.map { it.name }}")
    return stuck
  }


  /** The clauses of a split on [match]'s matched arguments: one per combination of their constructors. */
  private fun matchClauses(goal: ArendGoal, match: Match, extraPatterns: (ConcreteFactory, Names) -> List<ConcretePattern> = { _, _ -> emptyList() }): List<ConcreteClause>? {
    val factory = goal.typechecker.factory
    // The types of later parameters mention earlier ones
    val substitution = ExprSubstitution()
    match.params.zip(match.args).forEach { (param, arg) -> substitution.add(param, arg) }
    val alternatives = match.matched.map { i ->
      val type = match.params[i].type.subst(substitution).normalize(NormalizationMode.WHNF) as? DataCallExpression ?: return null
      constructors(type)?.takeIf { it.isNotEmpty() } ?: return null
    }
    if (alternatives.fold(1) { n, it -> n * it.size } > MAX_CLAUSES) return null
    var rows: List<List<ConCallExpression>> = listOf(emptyList())
    for (alternative in alternatives) rows = rows.flatMap { row -> alternative.map { row + it } }
    return rows.map { row ->
      val names = Names(goal)
      factory.clause(row.map { constructorPattern(factory, names, it) } + extraPatterns(factory, names), factory.goal())
    }
  }

  private fun mcasesSteps(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val mcases = mcases ?: return emptyList()
    val factory = goal.typechecker.factory
    // No check against enclosing splits: in its branches the stuck expression has computed away
    return stuckMatches(goal).mapNotNull { match ->
      val clauses = matchClauses(goal, match) ?: return@mapNotNull null
      // The form the meta's resolver produces: `mcases {spec} () \with {...}`, where the spec selects the
      // k-th \case expression (`{k}`) or the k-th call of f (`{(f, k)}`); an occurrence at a time, since
      // matching several at once multiplies the patterns of every clause
      val occurrence = factory.number(match.occurrence)
      val spec = match.definition?.let { factory.tuple(factory.ref(it.ref), occurrence) } ?: occurrence
      val term = factory.app(factory.ref(mcases), listOf(factory.arg(spec, false)) + listOf(
        factory.arg(factory.tuple(), true),
        factory.arg(factory.caseExpr(false, emptyList(), null, null, clauses), true),
      ))
      build(goal, currentProof, term, MCASES_COST)
    }
  }

  // ── \case e \as x, idp : e = x: a compound expression of the goal ──

  /**
   * The compound expressions of a data type in the goal, outermost first: applications that are
   * neither a variable, a constructor nor a numeral, such as `x Nat.- y` or `isPrime n`.
   */
  private fun compoundExpressions(goal: ArendGoal): List<Expression> {
    val found = LinkedHashMap<String, Expression>()
    goal.expectedType.accept(object : VoidExpressionVisitor<Void?>() {
      private fun consider(expr: Expression) {
        if (found.size >= MAX_COMPOUND) return
        val type = expr.type?.normalize(NormalizationMode.WHNF) as? DataCallExpression ?: return
        // A proposition is a hypothesis to split, not a value to compute with
        if (type.sortOfType?.isProp == true) return
        if (constructors(type).isNullOrEmpty()) return
        // The length of an array variable, `l.len` in `Fin l.len`, is refined by splitting the array (arend-lib's
        // `\elim l` in `BigSum_zro`, `fit_BigSum`), never by a case on the length
        if (expr is FieldCallExpression && expr.argument is ReferenceExpression &&
          (expr.argument.type?.normalize(NormalizationMode.WHNF) as? ClassCallExpression)?.definition == Prelude.DEP_ARRAY) return
        found.putIfAbsent(expr.toString(), expr)
      }

      override fun visitFunCall(expr: FunCallExpression, params: Void?): Void? { consider(expr); return super.visitFunCall(expr, params) }
      override fun visitFieldCall(expr: FieldCallExpression, params: Void?): Void? { consider(expr); return super.visitFieldCall(expr, params) }
      override fun visitApp(expr: AppExpression, params: Void?): Void? { consider(expr); return super.visitApp(expr, params) }
    }, null)
    return found.values.toList()
  }

  private fun compoundSteps(goal: ArendGoal, currentProof: Proof<ArendGoal>?, alreadySplit: Set<String>): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    return compoundExpressions(goal).mapNotNull { expr ->
      if (expr.toString() in alreadySplit) return@mapNotNull null
      val type = expr.type.normalize(NormalizationMode.WHNF) as? DataCallExpression ?: return@mapNotNull null
      val alternatives = constructors(type) ?: return@mapNotNull null
      if (alternatives.size > MAX_CLAUSES) return@mapNotNull null
      val asName = Names(goal).fresh("x")
      val asRef = factory.local(asName)
      val coreExpr = CoreToConcrete.convert(expr, goal) ?: return@mapNotNull null
      // `idp : e = x` is kept in every clause as the equation between `e` and the constructor matched
      val equation = factory.app(factory.ref(Prelude.PATH_INFIX.ref), true, coreExpr, factory.ref(asRef))
      val arguments = listOf(
        factory.caseArg(coreExpr, asRef, null),
        factory.caseArg(factory.ref(Prelude.IDP.ref), null, equation),
      )
      val clauses = alternatives.map { conCall ->
        val names = Names(goal)
        names.fresh(asName)
        factory.clause(listOf(constructorPattern(factory, names, conCall), factory.refPattern(factory.local(names.fresh("p")), null)), factory.goal())
      }
      build(goal, currentProof, factory.caseExpr(false, arguments, null, null, clauses), COMPOUND_COST)
    }
  }

  /** The key of the arguments of a decision `f x y`, such that decisions on the same elements share it. */
  private fun decisionKey(arguments: List<String>): String = "decision on " + arguments.sorted().joinToString(" ")

  /** A `\case` argument as text; a core expression wrapped for the typechecker prints as that expression. */
  private fun argumentKey(expr: Concrete.Expression): String =
    ((expr as? Concrete.ReferenceExpression)?.referent as? CoreReferable)?.result?.expression?.toString() ?: expr.toString()

  private fun decisionArguments(expr: Concrete.Expression): List<String> =
    if (expr is Concrete.AppExpression) listOf(decisionKey(expr.arguments.map { it.expression.toString() })) else emptyList()

  /**
   * Whether [goal] sits directly under a binder of [currentProof]: the root, a `\case` clause or a
   * lambda body, with no application, tuple or other construct between them.
   */
  private fun directlyUnderBinder(goal: ArendGoal, currentProof: Proof<ArendGoal>?): Boolean {
    val proof = currentProof as? ArendProof ?: return true
    val target = proof.getGoals()[goal] ?: return true
    var result = true
    proof.getProof()?.accept(object : BaseConcreteExpressionVisitor<Boolean>() {
      override fun visitGoal(expr: Concrete.GoalExpression, underBinder: Boolean): Concrete.Expression {
        if (expr === target) result = underBinder
        return expr
      }

      override fun visitCase(expr: Concrete.CaseExpression, underBinder: Boolean): Concrete.Expression {
        expr.arguments.forEach { it.expression.accept(this, false) }
        expr.clauses.forEach { it.expression?.accept(this, true) }
        return expr
      }

      override fun visitLam(expr: Concrete.LamExpression, underBinder: Boolean): Concrete.Expression {
        expr.body.accept(this, true)
        return expr
      }

      override fun visitApp(expr: Concrete.AppExpression, underBinder: Boolean): Concrete.Expression = super.visitApp(expr, false)
      override fun visitTuple(expr: Concrete.TupleExpression, underBinder: Boolean): Concrete.Expression = super.visitTuple(expr, false)
    }, true)
    return result
  }

  /**
   * The arguments, as text, of the `\case` expressions of [currentProof] that enclose [goal],
   * and the [decisionKey] of each that is a decision.
   */
  private fun enclosingCaseArguments(goal: ArendGoal, currentProof: Proof<ArendGoal>?): Set<String> {
    val proof = currentProof as? ArendProof ?: return emptySet()
    val target = proof.getGoals()[goal] ?: return emptySet()
    val enclosing = ArrayDeque<List<String>>()
    var found: Set<String> = emptySet()
    proof.getProof()?.accept(object : BaseConcreteExpressionVisitor<Void?>() {
      override fun visitCase(expr: Concrete.CaseExpression, params: Void?): Concrete.Expression {
        // Per clause: an argument matched by a plain variable pattern, as the `x` of `\case \elim n, \elim x`
        // that only goes along with `n`, is not split in that clause and may be split inside it
        for (clause in expr.clauses) {
          enclosing.addLast(expr.arguments.withIndex().flatMap { (i, argument) ->
            val split = clause.patterns.getOrNull(i) !is Concrete.NamePattern
            (if (split) listOf(argumentKey(argument.expression)) else emptyList()) + decisionArguments(argument.expression)
          })
          try {
            clause.expression?.accept(this, params)
          } finally {
            enclosing.removeLast()
          }
        }
        return expr
      }

      override fun visitGoal(expr: Concrete.GoalExpression, params: Void?): Concrete.Expression {
        if (expr === target) found = enclosing.flatten().toSet()
        return super.visitGoal(expr, params)
      }
    }, null)
    return found
  }

  private fun build(goal: ArendGoal, currentProof: Proof<ArendGoal>?, term: ConcreteExpression, cost: Double) =
    StepBuilder.build(goal, currentProof, term, cost, moduleLocation)

  private fun emptyCase(goal: ArendGoal, ref: Referable): ConcreteExpression {
    val factory = goal.typechecker.factory
    return factory.caseExpr(false, listOf(factory.caseArg(factory.ref(ref), null, null)), null, null, emptyList<ConcreteClause>())
  }

  /** Whether no constructor can produce a value of [type]. */
  private fun isAbsurd(type: Expression): Boolean {
    RewriteGenerator.equationSides(type)?.let { (left, right) ->
      // a = b between different constructors, e.g. suc n = 0
      val leftConstructor = constructorOf(left.normalize(NormalizationMode.WHNF)) ?: return false
      return leftConstructor != (constructorOf(right.normalize(NormalizationMode.WHNF)) ?: return false)
    }
    return type is DataCallExpression && type.matchedConstructors?.isEmpty() == true
  }

  /** The constructor at the head of [expr], counting numerals as `zero` and `suc`. */
  private fun constructorOf(expr: Expression): Constructor? = when (expr) {
    is ConCallExpression -> expr.definition
    is IntegerExpression -> if (expr.isZero) Prelude.ZERO else Prelude.SUC
    else -> null
  }

  /**
   * The constructors that can produce a value of [type], or null if they cannot be determined.
   * Path constructors such as `truncP` of `TruncP` are left out: the types split here are
   * propositions or sets, for which arend-lib proofs omit their clauses.
   */
  private fun constructors(type: DataCallExpression): List<ConCallExpression>? =
    type.matchedConstructors?.filter { !isPathConstructor(it.definition) }

  /** A path constructor is represented with an interval parameter. */
  private fun isPathConstructor(constructor: Constructor): Boolean =
    DependentLink.Helper.toList(constructor.parameters).any { (it.type as? DataCallExpression)?.definition == Prelude.INTERVAL }

  private fun isRecursive(data: DataDefinition): Boolean = data.constructors.filter { !isPathConstructor(it) }.any { constructor ->
    DependentLink.Helper.toList(constructor.parameters).any { param ->
      var found = false
      param.type.accept(object : org.arend.core.expr.visitor.VoidExpressionVisitor<Void?>() {
        override fun visitDefCall(expr: DefCallExpression, params: Void?): Void? {
          if (expr.definition == data) found = true
          return super.visitDefCall(expr, params)
        }
      }, null)
      found
    }
  }

  private fun splitBinding(
    goal: ArendGoal, currentProof: Proof<ArendGoal>?, context: List<Pair<Referable, Binding>>,
    ref: Referable, binding: Binding, type: Expression, stuckOn: Boolean = false, alreadySplit: Set<String> = emptySet(),
    enclosingHypothesisSplits: List<Int> = emptyList(),
  ): ProofStep<ArendGoal>? {
    // Hypotheses depending on the variable, and on those (`p : x = y` for `x y : Fin n` when `n` is split): eliminated with it
    var dependents = context.filter { (_, other) -> other != binding && StepBuilder.occurs(binding, other.type) }
    while (true) {
      val more = context.filter { (_, other) -> other != binding && other !in dependents.map { it.second } && dependents.any { (_, d) -> StepBuilder.occurs(d, other.type) } }
      if (more.isEmpty()) break
      dependents = context.filter { it in dependents || it in more }
    }
    val occursInGoal = StepBuilder.occurs(binding, goal.expectedType)
    val elim = occursInGoal || dependents.isNotEmpty()
    // A hypothesis is split after the hypotheses before it in the context, not before them
    if (!occursInGoal && enclosingHypothesisSplits.any { it > context.indexOfFirst { (_, other) -> other == binding } }) return null

    val factory = goal.typechecker.factory
    val names = Names(goal, if (elim) ref.refName else null)
    // Eliminated before the variable itself: the length of an array, which its patterns depend on
    var leading: List<Pair<Referable, List<ConcretePattern>>> = emptyList()
    val clauses: List<ConcreteClause> = when (type) {
      is SigmaExpression -> listOf(factory.clause(listOf(tuplePattern(factory, names, type)) + dependents.map { factory.refPattern(factory.local(it.first.refName), null) }, factory.goal()))
      is ClassCallExpression -> {
        // An array is matched by `nil` and `a :: l`; one of a fixed length by the patterns of that length
        if (type.definition != Prelude.DEP_ARRAY || !elim) return null
        val length = type.getAbsImplementationHere(Prelude.ARRAY_LENGTH)?.normalize(NormalizationMode.WHNF)
        fun nil() = factory.conPattern(Prelude.EMPTY_ARRAY.ref, emptyList())
        fun cons() = factory.conPattern(Prelude.ARRAY_CONS.ref, listOf(
          factory.refPattern(factory.local(names.fresh("a")), null), factory.refPattern(factory.local(names.fresh(null)), null)))
        val patterns: List<List<ConcretePattern>> = when {
          length == null -> listOf(listOf(nil()), listOf(cons()))
          length is IntegerExpression -> listOf(listOf(if (length.isZero) nil() else cons()))
          length is ConCallExpression && length.definition == Prelude.SUC -> listOf(listOf(cons()))
          length is ConCallExpression && length.definition == Prelude.ZERO -> listOf(listOf(nil()))
          length is ReferenceExpression -> {
            // `Array A n` splits with its length: `\case \elim n, \elim l \with { | 0, nil => .. | suc n, a :: l => .. }`
            val (lengthRef, lengthBinding) = context.find { it.second == length.binding } ?: return null
            if (lengthRef.refName in alreadySplit) return null
            val lengthDependents = context.filter { (_, other) -> other != lengthBinding && other != binding && StepBuilder.occurs(lengthBinding, other.type) }
            // In context order, which is a valid telescope: `p : l i = l' i` has to come after `l'`
            dependents = context.filter { it in dependents || it in lengthDependents }
            names.release(lengthRef.refName)
            val n = names.fresh(lengthRef.refName)
            leading = listOf(lengthRef to listOf(factory.numberPattern(0), factory.conPattern(Prelude.SUC.ref, listOf(factory.refPattern(factory.local(n), null)))))
            listOf(listOf(nil()), listOf(cons()))
          }
          else -> return null
        }
        patterns.mapIndexed { i, pattern ->
          factory.clause(leading.map { it.second[i] } + pattern + dependents.map { factory.refPattern(factory.local(it.first.refName), null) }, factory.goal())
        }
      }
      is DataCallExpression -> {
        // Equations are rewritten with rather than split
        if (RewriteGenerator.equationSides(type) != null) return null
        val constructors = constructors(type) ?: return null
        // A variable that does not occur anywhere is only worth splitting when the split cannot recurse
        // (Or, Dec, Tri, ...), or when its indices rule out constructors, as for `p : suc n < suc m`
        val refines = constructors.size < type.definition.constructors.count { !isPathConstructor(it) }
        if (!elim && !refines && isRecursive(type.definition)) return null
        // Splitting a hypothesis into a single constructor without fields, as `a : All P nil` into `all-nil`, binds nothing new
        if (!elim && constructors.size == 1 && DependentLink.Helper.toList(constructors[0].definition.parameters).none { it.isExplicit }) return null
        constructors.map { constructor ->
          val patterns = listOf(constructorPattern(factory, names, constructor)) + dependents.map { factory.refPattern(factory.local(it.first.refName), null) }
          factory.clause(patterns, factory.goal())
        }
      }
      else -> return null
    }
    val arguments: List<ConcreteCaseArgument> = (leading.map { it.first } + ref + dependents.map { it.first }).map {
      Concrete.CaseArgument(factory.ref(it) as Concrete.Expression, null, null, elim, BindingVariance.INVARIANT)
    }
    // Splitting what the goal is stuck on, or a hypothesis, makes progress by itself; splitting another
    // variable of the goal only sometimes does, so it pays for its clauses in full
    val discount = if (stuckOn || !occursInGoal) CLAUSE_DISCOUNT * (min(clauses.size, MAX_DISCOUNTED_CLAUSES) - 1) else 0.0
    val cost = (if (occursInGoal) VARIABLE_COST else HYPOTHESIS_COST) - (if (stuckOn) STUCK_BONUS else 0.0) - discount
    return build(goal, currentProof, factory.caseExpr(false, arguments, null, null, clauses), cost)
  }

  /** `c x1 ... xn` for the constructor of [conCall]; an argument of a `\Sigma` type is matched by a tuple, as in `inP (a, p)`. */
  private fun constructorPattern(factory: ConcreteFactory, names: Names, conCall: ConCallExpression): ConcretePattern {
    val constructor = conCall.definition
    // The parameter types mention the data type's parameters, e.g. `inP (a : A)` for `TruncP A`
    val substitution = ExprSubstitution()
    DependentLink.Helper.toList(constructor.dataTypeParameters).zip(conCall.dataTypeArguments).forEach { (param, arg) -> substitution.add(param, arg) }
    val params = DependentLink.Helper.toList(DependentLink.Helper.subst(constructor.parameters, substitution, LevelSubstitution.EMPTY))
    val subpatterns = params.filter { it.isExplicit }.map { param ->
      val paramType = param.type.normalize(NormalizationMode.WHNF)
      // An argument of the data type itself, as the tail of `x :: l`, takes the eliminated variable's name
      val recursive = (paramType as? DataCallExpression)?.definition == constructor.dataType
      if (paramType is SigmaExpression) tuplePattern(factory, names, paramType) else variablePattern(factory, names, param, recursive)
    }
    return factory.conPattern(constructor.ref, subpatterns)
  }

  private fun tuplePattern(factory: ConcreteFactory, names: Names, type: SigmaExpression): ConcretePattern =
    factory.tuplePattern(DependentLink.Helper.toList(type.parameters).map { variablePattern(factory, names, it) })

  /** A variable named after [param], or `p` for an unnamed proof and `x` for other unnamed values. */
  private fun variablePattern(factory: ConcreteFactory, names: Names, param: DependentLink, recursive: Boolean = false): ConcretePattern {
    val base = param.name ?: if (recursive) names.eliminated else if (param.type.sortOfType?.isProp == true) "p" else "x"
    return factory.refPattern(factory.local(names.fresh(base)), null)
  }

  /** `\case splitter x... \with { ... }`, with a clause for each constructor of the result type. */
  private fun splitOnApplication(goal: ArendGoal, currentProof: Proof<ArendGoal>?, splitter: ArendRef, args: List<Referable>, goalIsProp: Boolean, cost: Double, alreadySplit: Set<String>): ProofStep<ArendGoal>? {
    val factory = goal.typechecker.factory
    val application = factory.app(factory.ref(splitter), true, args.map { factory.ref(it) })
    // Once a decision on these elements is taken, another one only multiplies the branches
    if (decisionKey(args.map { it.refName }) in alreadySplit) return null
    val errorReporter = ListErrorReporter()
    val branchTC = CheckTypeVisitor.loadTypecheckingContext(goal.typechecker.saveTypecheckingContext(), errorReporter)
    val typed = try { branchTC.finalize(branchTC.typecheck(application, null), application as Concrete.SourceNode) } catch (e: Exception) { null }
    if (typed == null || branchTC.status.hasErrors() || errorReporter.errorList.any { it.level == GeneralError.Level.ERROR }) return null
    val type = typed.type.normalize(NormalizationMode.WHNF)
    if (type !is DataCallExpression || RewriteGenerator.equationSides(type) != null) return null
    if (type.sortOfType?.isProp == true && !goalIsProp) return null
    val constructors = constructors(type) ?: return null

    val names = Names(goal)
    val clauses = constructors.map { factory.clause(listOf(constructorPattern(factory, names, it)), factory.goal()) }
    val relevant = EquationRetriever.functionNames(type).any { it in EquationRetriever.functionNames(goal.expectedType) }
    return build(goal, currentProof, factory.caseExpr(false, listOf(factory.caseArg(application, null, null)), null, null, clauses), cost - if (relevant) RELEVANT_BONUS else 0.0)
  }
}
