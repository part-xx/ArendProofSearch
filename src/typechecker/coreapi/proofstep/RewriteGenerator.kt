package typechecker.coreapi.proofstep

import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.FunCallExpression
import org.arend.core.expr.PathTypeExpression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.ReferenceExpression
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import org.arend.prelude.Prelude
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof
import org.arend.term.concrete.Concrete

/** The metas of arend-lib's `Paths.Meta` and `Meta` that rewriting is written with. */
class RewriteMetas(val rewrite: ArendRef, val rewriteI: ArendRef, val inMeta: ArendRef? = null)

/**
 * Rewriting, in the shapes arend-lib proofs use:
 *
 * - `rewrite p {?}` / `rewriteI p {?}` for an equation `p : a = b` of the context, which replaces
 *   `a` by `b` (`b` by `a`) in the goal; such equations usually come from a case split
 *   (`suc<=suc`, `toZero`, `real_join_L`);
 * - `rewrite p in h` / `rewriteI p in h`, which closes the goal with a hypothesis `h` rewritten by
 *   `p` (`Int.conv`, `div-unique`);
 * - `rewrite L {?}` / `rewriteI L {?}` for a library equation `L` among [lemmas], whose arguments
 *   the meta infers from the first match (`+-comm`, `*-assoc`, `ide-left`, `-'0`). A direction is
 *   skipped when the side it replaces is a bare variable: it would match any subterm.
 *
 * When a rewrite is proposed follows how arend-lib uses it. An equation `p : a = b` of the context
 * is rewritten with in the direction that replaces a side occurring in the goal: `rewrite p` when
 * `a` occurs, `rewriteI p` when `b` does (`rewrite p <=-refl` after `inr p : x = y`, `rewrite p
 * (byRight zero<suc)` after `p : n -' m = suc x`). `rewrite p in h` transports a hypothesis `h`
 * whose type mentions the side to the goal, so it is proposed when the side occurs in `h` and the
 * rewritten `h` has the goal's head (`rewrite n=m in p` for `<-irreflexive`, `rewriteI p in h`).
 * A library equation is rewritten with in the direction whose side matches a subterm of the
 * goal, and the matching sides are never bare parameters.
 */
class RewriteGenerator(
  private val moduleLocation: ModuleLocation,
  private val metas: RewriteMetas,
  private val lemmas: List<CallableDefinition> = emptyList(),
  private val lemmaCosts: Map<CallableDefinition, Double> = emptyMap()
) : ProofStepGenerator<ArendGoal> {
  companion object {
    const val HYPOTHESIS_COST = 1.0
    const val IN_HYPOTHESIS_COST = 0.5
    const val LEMMA_COST = 1.5
    /**
     * Added for a permutative equation, one whose sides have the same head (`x ∧ y = y ∧ x`,
     * `x + (y + z) = (x + y) + z`): arend-lib rewrites with those inside a chain that leads
     * somewhere, rarely as the first step, and they can be applied without end.
     */
    const val PERMUTATIVE_COST = 0.4

    /** The sides `a`, `b` of an equation type `a = b`, or null if [type] is not one. */
    fun equationSides(type: Expression): Pair<Expression, Expression>? {
      (type as? PathTypeExpression)?.let { return it.leftArgument to it.rightArgument }
      val call = (type as? FunCallExpression)?.takeIf { it.definition == Prelude.PATH_INFIX }
        ?: (type.normalize(NormalizationMode.WHNF) as? DefCallExpression)?.takeIf { it.definition == Prelude.PATH }
        ?: return (type.normalize(NormalizationMode.WHNF) as? PathTypeExpression)?.let { it.leftArgument to it.rightArgument }
      val args = call.defCallArguments
      return args[args.size - 2] to args[args.size - 1]
    }

    /** [equationSides] without normalizing: the equation as written, `a = b`, `Path`, or a path type. */
    fun equationSidesAsWritten(type: Expression): Pair<Expression, Expression>? {
      (type as? PathTypeExpression)?.let { return it.leftArgument to it.rightArgument }
      val call = (type as? FunCallExpression)?.takeIf { it.definition == Prelude.PATH_INFIX }
        ?: (type as? DefCallExpression)?.takeIf { it.definition == Prelude.PATH }
        ?: return null
      val args = call.defCallArguments
      return args[args.size - 2] to args[args.size - 1]
    }

    /** The type the sides of the equation [type] are compared in (`Nat` in `x = {Nat} y` for `x y : Fin n`), or null if [type] is not an equation. */
    fun equationType(type: Expression): Expression? {
      fun ofPath(path: PathTypeExpression): Expression = (path.argumentType as? org.arend.core.expr.LamExpression)?.body ?: path.argumentType
      (type as? PathTypeExpression)?.let { return ofPath(it) }
      val call = (type as? FunCallExpression)?.takeIf { it.definition == Prelude.PATH_INFIX }
        ?: (type.normalize(NormalizationMode.WHNF) as? DefCallExpression)?.takeIf { it.definition == Prelude.PATH }
        ?: return (type.normalize(NormalizationMode.WHNF) as? PathTypeExpression)?.let { ofPath(it) }
      val first = call.defCallArguments.firstOrNull() ?: return null
      return (first as? org.arend.core.expr.LamExpression)?.body ?: first
    }

    /** The equation [lemma] concludes, after its parameters. */
    fun lemmaSides(lemma: CallableDefinition): Pair<Expression, Expression>? {
      var type: Expression = when (lemma) {
        is FunctionDefinition -> lemma.resultType ?: return null
        is ClassField -> lemma.type.codomain
        else -> return null
      }
      while (true) {
        type = (type as? PiExpression)?.codomain ?: break
      }
      return equationSides(type)
    }
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    fun add(term: ConcreteExpression, cost: Double) {
      StepBuilder.build(goal, currentProof, term, cost, moduleLocation)?.let { steps.add(it) }
    }
    fun rewriteStep(meta: ArendRef, equation: ConcreteExpression) = factory.app(factory.ref(meta), true, equation, factory.goal())

    val context = StepBuilder.context(goal)
    val goalHead = PremiseRetriever.headKey(goal.expectedType)
    // An equation rewritten with just before is not rewritten with the other way: that undoes the
    // rewrite (`rewrite p (rewriteI p {?})`); the same way again may reach a second occurrence (`-'0`)
    val used = enclosingRewrites(goal, currentProof)
    fun undoes(meta: ArendRef, name: String) = (if (meta == metas.rewrite) metas.rewriteI else metas.rewrite).refName to name in used
    for ((p, binding) in context) {
      val (left, right) = equationSides(binding.type) ?: continue
      // The direction that replaces a side the goal has
      if (ConclusionMatcher.occursIn(left, goal.expectedType) && !undoes(metas.rewrite, p.refName)) add(rewriteStep(metas.rewrite, factory.ref(p)), HYPOTHESIS_COST)
      if (ConclusionMatcher.occursIn(right, goal.expectedType) && !undoes(metas.rewriteI, p.refName)) add(rewriteStep(metas.rewriteI, factory.ref(p)), HYPOTHESIS_COST)
      val inMeta = metas.inMeta ?: continue
      // A hypothesis of the goal's kind that mentions a side becomes the goal once the side is replaced
      for ((h, hBinding) in context) {
        if (h == p || goalHead == null || PremiseRetriever.headKey(hBinding.type) != goalHead) continue
        if (ConclusionMatcher.occursIn(left, hBinding.type)) add(factory.app(factory.ref(inMeta), true, factory.app(factory.ref(metas.rewrite), true, factory.ref(p)), factory.ref(h)), IN_HYPOTHESIS_COST)
        if (ConclusionMatcher.occursIn(right, hBinding.type)) add(factory.app(factory.ref(inMeta), true, factory.app(factory.ref(metas.rewriteI), true, factory.ref(p)), factory.ref(h)), IN_HYPOTHESIS_COST)
      }
    }

    for (lemma in lemmas) {
      val (leftScore, rightScore) = ConclusionMatcher.rewriteSideScores(lemma, goal.expectedType) ?: continue
      val sides = lemmaSides(lemma)
      val permutative = sides != null && PremiseRetriever.head(sides.first) != null && PremiseRetriever.head(sides.first) == PremiseRetriever.head(sides.second)
      val cost = (lemmaCosts[lemma] ?: LEMMA_COST) + (if (permutative) PERMUTATIVE_COST else 0.0)
      if (leftScore != null && !undoes(metas.rewrite, lemma.ref.refName)) add(rewriteStep(metas.rewrite, factory.ref(lemma.ref)), cost)
      if (rightScore != null && !undoes(metas.rewriteI, lemma.ref.refName)) add(rewriteStep(metas.rewriteI, factory.ref(lemma.ref)), cost)
    }
    return steps
  }

  /**
   * The `rewrite` and `rewriteI` applications the goal is the direct argument of, through a chain of
   * them, as the meta's name with the equation's: (`rewrite`, `p`) and (`rewriteI`, `L`) for the goal
   * in `rewrite p (rewriteI L {?})`.
   */
  private fun enclosingRewrites(goal: ArendGoal, currentProof: Proof<ArendGoal>?): Set<Pair<String, String>> {
    val proof = currentProof as? ArendProof ?: return emptySet()
    val target = proof.getGoals()[goal] ?: return emptySet()
    val rewriteNames = setOf(metas.rewrite.refName, metas.rewriteI.refName)
    /**
     * The rewrites enclosing the target inside [expr], innermost first, and whether the chain is
     * sealed by a node that is not a rewrite between them and the target; null if the target is not in [expr].
     */
    fun chain(expr: Concrete.Expression?): Pair<List<Pair<String, String>>, Boolean>? {
      if (expr == null) return null
      if (expr === target) return emptyList<Pair<String, String>>() to false
      fun sealed(inner: Pair<List<Pair<String, String>>, Boolean>?) = inner?.let { it.first to true }
      return when (expr) {
        is Concrete.AppExpression -> {
          val metaName = (expr.function as? Concrete.ReferenceExpression)?.referent?.refName?.takeIf { it in rewriteNames && expr.arguments.size >= 2 }
          for ((i, argument) in expr.arguments.withIndex()) {
            val (inner, isSealed) = chain(argument.expression) ?: continue
            if (metaName == null || i != expr.arguments.lastIndex || isSealed) return inner to true
            val equation = expr.arguments[0].expression
            return inner + (metaName to ((equation as? Concrete.ReferenceExpression)?.referent?.refName ?: equation.toString())) to false
          }
          sealed(chain(expr.function))
        }
        is Concrete.CaseExpression -> sealed(expr.clauses.firstNotNullOfOrNull { chain(it.expression) } ?: expr.arguments.firstNotNullOfOrNull { chain(it.expression) })
        is Concrete.LamExpression -> sealed(chain(expr.body))
        is Concrete.TupleExpression -> sealed(expr.fields.firstNotNullOfOrNull { chain(it) })
        else -> null
      }
    }
    return chain(proof.getProof())?.first?.toSet() ?: emptySet()
  }
}
