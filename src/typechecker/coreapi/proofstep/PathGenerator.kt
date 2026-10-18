package typechecker.coreapi.proofstep

import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.core.definition.CallableDefinition
import org.arend.core.expr.Expression
import org.arend.ext.module.ModuleLocation
import org.arend.ext.reference.ArendRef
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * Path chains through a hypothesis `p : a = b` for an equation goal `l = r`, in the shapes
 * arend-lib proofs take, each when its ends meet: `inv p` when `b = l` and `a = r`; `p *> {?}`
 * when `a = l`, `{?} *> p` when `b = r`; `inv p *> {?}` when `b = l`, `{?} *> inv p` when
 * `a = r`. `*>` and `inv` applied to holes alone are not proposed: the middle term of
 * `{?} *> {?}` cannot be inferred, and `inv {?}` only flips the goal.
 */
class PathGenerator(
  private val moduleLocation: ModuleLocation,
  private val concat: ArendRef,
  private val inv: ArendRef,
  private val cost: Double = 1.2,
  /** Library equations to chain through, as `+-assoc *> {?}`: those whose side matches an end of the goal. */
  private val lemmas: List<CallableDefinition> = emptyList(),
  private val lemmaCosts: Map<CallableDefinition, Double> = emptyMap(),
) : ProofStepGenerator<ArendGoal> {
  companion object {
    const val LEMMA_COST = 1.5
  }

  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val (left, right) = RewriteGenerator.equationSides(goal.expectedType) ?: return emptyList()
    val factory = goal.typechecker.factory
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    fun add(term: ConcreteExpression, stepCost: Double) {
      StepBuilder.build(goal, currentProof, term, stepCost, moduleLocation)?.let { steps.add(it) }
    }
    val same = PremiseRetriever::same
    for ((ref, binding) in StepBuilder.context(goal)) {
      val (a, b) = RewriteGenerator.equationSides(binding.type) ?: continue
      val hypothesis = factory.ref(ref)
      val flipped = factory.app(factory.ref(inv), true, factory.ref(ref))
      if (same(b, left) && same(a, right)) add(flipped, cost * AppGenerator.CLOSING_FACTOR)
      val chainCost = cost + AppGenerator.SUBGOAL_COST
      if (same(a, left)) add(factory.app(factory.ref(concat), true, hypothesis, factory.goal()), chainCost)
      if (same(b, right)) add(factory.app(factory.ref(concat), true, factory.goal(), hypothesis), chainCost)
      if (same(b, left)) add(factory.app(factory.ref(concat), true, flipped, factory.goal()), chainCost)
      if (same(a, right)) add(factory.app(factory.ref(concat), true, factory.goal(), flipped), chainCost)
    }
    // A library equation `L : l = r` starts or ends the chain where a side of it matches an end of the goal
    // (its parameters are inferred from that end): `rdistr *> {?}`, `{?} *> inv +-assoc`
    for (lemma in lemmas) {
      val (a, b) = RewriteGenerator.lemmaSides(lemma) ?: continue
      val chainCost = (lemmaCosts[lemma] ?: LEMMA_COST) + AppGenerator.SUBGOAL_COST
      val lemmaRef = factory.ref(lemma.ref)
      val flipped = factory.app(factory.ref(inv), true, factory.ref(lemma.ref))
      fun matches(side: Expression, end: Expression) = (ConclusionMatcher.match(side, end) ?: 0) >= 1
      if (matches(a, left)) add(factory.app(factory.ref(concat), true, lemmaRef, factory.goal()), chainCost)
      if (matches(b, right)) add(factory.app(factory.ref(concat), true, factory.goal(), lemmaRef), chainCost)
      if (matches(b, left)) add(factory.app(factory.ref(concat), true, flipped, factory.goal()), chainCost)
      if (matches(a, right)) add(factory.app(factory.ref(concat), true, factory.goal(), flipped), chainCost)
    }
    return steps
  }
}
