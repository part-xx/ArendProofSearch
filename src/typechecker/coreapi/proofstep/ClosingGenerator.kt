package typechecker.coreapi.proofstep

import org.arend.core.expr.DataCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.core.context.param.DependentLink
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.core.ops.CMP
import org.arend.typechecking.implicitargs.equations.DummyEquations
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.prelude.Prelude
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Closes a goal outright: with `idp`, with a hypothesis of the goal's type, or with one of
 * [closingMetas] (e.g. `contradiction`, which refutes the context). Most proofs in arend-lib
 * that rewrite or split end their branches this way.
 */
class ClosingGenerator(
  private val moduleLocation: ModuleLocation,
  /** Metas that close a goal, each with its cost: `contradiction`, and solvers such as `equation` and `linarith`. */
  private val closingMetas: List<Pair<ArendRef, Double>> = emptyList(),
  private val cost: Double = 0.0,
  /** arend-lib's `using` meta: with it, a solver is also given the context's equations, `equation {using (p, q)}`. */
  private val usingMeta: ArendRef? = null,
  /**
   * arend-lib's specialized equation solvers (`equation.group`, `equation.monoid`, ...), most specific class first:
   * they take hints in braces, `equation.group {pmap inverse p}` (`comm_sym`), `equation.monoid {p, pow-comm1 p}`.
   */
  private val solvers: List<Solver> = emptyList(),
  /** arend-lib's `pmap`, for hints derived from the hypotheses: `pmap (* h) p` (`comm_conjugate`). */
  private val pmap: ArendRef? = null,
  /** Lemma instances to hint a solver with, `pow-comm1 (inv p)` ([LemmaHints]); computed only when a solver applies. */
  private val lemmaHints: () -> List<ConcreteExpression> = { emptyList() },
) : ProofStepGenerator<ArendGoal> {
  /** A specialized solver with the class whose instances it is for. */
  class Solver(val meta: ArendRef, val classDefinition: org.arend.core.definition.ClassDefinition)

  companion object {
    /** Added to a solver's cost when it is given the context's equations as hints. */
    const val HINTS_EXTRA_COST = 0.2
    /** Added when the hint is derived from a hypothesis, `pmap inverse p`. */
    const val DERIVED_HINT_COST = 0.2
    /** Added when the hints are lemma instances, `pow-comm1 (inv p)`. */
    const val LEMMA_HINT_COST = 0.2
    /** At most this many elements of the carrier are tried in a section `(* x)` of a derived hint. */
    const val MAX_SECTION_ELEMENTS = 6

    /**
     * The specialized solver for an equation goal in the carrier of a class instance, by the class, with the
     * instance's class: `equation.group` for `E : Group`, `equation.addGroup` for `AddGroup`, or null.
     */
    fun solverFor(goal: ArendGoal, solvers: List<Solver>): Pair<Solver, org.arend.core.expr.FieldCallExpression>? {
      val (left, _) = RewriteGenerator.equationSides(goal.expectedType) ?: return null
      val carrier = (RewriteGenerator.equationType(goal.expectedType) ?: left.type) as? org.arend.core.expr.FieldCallExpression ?: return null
      val instanceClass = (carrier.argument.type?.normalize(NormalizationMode.WHNF) as? org.arend.core.expr.ClassCallExpression)?.definition ?: return null
      return solvers.firstOrNull { instanceClass.isSubClassOf(it.classDefinition) }?.let { it to carrier }
    }

    /** `solver {hint}`, or `solver {(h1, h2)}` for several hints. */
    fun hinted(factory: org.arend.ext.concrete.ConcreteFactory, solver: Solver, hints: List<ConcreteExpression>): ConcreteExpression =
      factory.app(factory.ref(solver.meta), false, if (hints.size == 1) hints[0] else factory.tuple(hints))
    /** The solvers that take `{using (...)}` hints, by name. */
    val HINTED_SOLVERS = setOf("equation")
    /** The orders `linarith` decides, by name. */
    val ORDER_RELATIONS = setOf("<", "<=", ">", ">=")

    /**
     * Whether the solver or refuter [meta] can address [goal] at all, by the goal's shape:
     * `equation` proves equations, `linarith` equations, linear inequalities and refutations
     * (its own words: "either an equation or the empty type"), `contradiction` anything.
     */
    fun addresses(meta: ArendRef, goal: ArendGoal): Boolean {
      val type = StepBuilder.unfold(goal.expectedType)
      val isEquation = RewriteGenerator.equationSides(type) != null
      return when (meta.refName) {
        "equation" -> isEquation
        "linarith" -> isEquation || PremiseRetriever.headName(type) in ORDER_RELATIONS || concludesEmpty(type)
        else -> true
      }
    }

    /** Whether [type] is `Empty`, or a function type into it (`Not A`, `a /= b`). */
    private fun concludesEmpty(type: Expression): Boolean {
      var current = type
      while (current is PiExpression) current = StepBuilder.unfold(current.codomain)
      return (current as? DataCallExpression)?.definition?.let { it.ref.refName == "Empty" && it.constructors.isEmpty() } == true
    }
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    val context = StepBuilder.context(goal)
    val equations = context.filter { (_, binding) -> RewriteGenerator.equationSides(binding.type) != null }.map { factory.ref(it.first) }
    val terms = listOf(factory.ref(Prelude.IDP.ref) to cost) +
      context.map { (ref, _) -> factory.ref(ref) to cost } +
      closingMetas.filter { (meta, _) -> addresses(meta, goal) }.map { (meta, metaCost) -> factory.ref(meta) to metaCost } +
      closingMetas.filter { (meta, _) -> usingMeta != null && meta.refName in HINTED_SOLVERS && equations.isNotEmpty() && addresses(meta, goal) }.map { (meta, metaCost) ->
        // `equation {using (p, q)}`: the hypotheses the solver may use besides the axioms
        val hints = if (equations.size == 1) equations[0] else factory.tuple(equations)
        factory.app(factory.ref(meta), false, factory.app(factory.ref(usingMeta!!), true, hints)) to metaCost + HINTS_EXTRA_COST
      }
    // One closing term is enough: the goal is solved, and the others would only duplicate the state
    for ((term, termCost) in terms) {
      StepBuilder.build(goal, currentProof, term, termCost, moduleLocation)?.let { return listOf(it) }
    }
    // The specialized solver of the goal's class with the hypotheses as hints, then with hints derived from
    // them: the hypothesis mapped over the class's unary operation (`pmap inverse p`) or over a section of its
    // binary operation at an element at hand (`pmap (* h) p`)
    val (solver, carrier) = solverFor(goal, solvers) ?: return emptyList()
    val solverCost = closingMetas.firstOrNull { it.first.refName == "equation" }?.second ?: cost
    if (equations.isNotEmpty()) {
      StepBuilder.build(goal, currentProof, hinted(factory, solver, equations), solverCost + HINTS_EXTRA_COST, moduleLocation)?.let { return listOf(it) }
    }
    // Lemmas applied to the hypotheses as further hints, each alone and then all together:
    // `equation.monoid {p, pow-comm1 p}` (`pow-comm1`), `equation {usingOnly (finv-right xi, finv-right x+1i, ...)}` (`finv-diff`)
    // The solver rewrites with its hints in order and fails when one no longer occurs, so each group is also tried without the hypotheses
    val instances = lemmaHints()
    for (group in LemmaHints.groups(instances)) {
      for (hints in listOf(equations + group, group).distinct()) {
        StepBuilder.build(goal, currentProof, hinted(factory, solver, hints), solverCost + HINTS_EXTRA_COST + LEMMA_HINT_COST, moduleLocation)?.let { return listOf(it) }
      }
    }
    if (pmap == null || equations.isEmpty()) return emptyList()
    val carrierType: Expression = carrier
    fun sameType(type: Expression?) = type != null && CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, type, carrierType, null, null)
    val fields: List<org.arend.core.definition.ClassField> = solver.classDefinition.allFields.toList()
    val unary = fields.filter { field -> field.name in setOf("inverse", "negative") && (field.type.codomain as? PiExpression)?.let { pi -> pi.parameters.isExplicit && DependentLink.Helper.toList(pi.parameters).size == 1 && pi.codomain !is PiExpression } == true }
    val binary = fields.filter { field -> field.name in setOf("*", "+") }
    val elements = (context.filter { (_, binding) -> sameType(binding.type) }.map { factory.ref(it.first) } +
      ConclusionMatcher.subterms(goal.expectedType).drop(1).filter { it !is ReferenceExpression && sameType(it.type) }.mapNotNull { CoreToConcrete.convert(it, goal) })
      .distinctBy { it.toString() }.take(MAX_SECTION_ELEMENTS)
    val functions = unary.map { factory.ref(it.ref) } + binary.flatMap { op ->
      elements.flatMap { x ->
        val z = factory.local("z")
        listOf(factory.lam(listOf(factory.param(true, z)), factory.app(factory.ref(op.ref), true, factory.ref(z), x)), factory.lam(listOf(factory.param(true, z)), factory.app(factory.ref(op.ref), true, x, factory.ref(z))))
      }
    }
    for (equation in equations) {
      for (function in functions) {
        val hint = factory.app(factory.ref(pmap), true, function, equation)
        StepBuilder.build(goal, currentProof, hinted(factory, solver, listOf(hint)), solverCost + HINTS_EXTRA_COST + DERIVED_HINT_COST, moduleLocation)?.let { return listOf(it) }
      }
    }
    return emptyList()
  }
}
