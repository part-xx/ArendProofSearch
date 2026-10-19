package typechecker.coreapi.proofstep

import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.visitor.CompareVisitor
import org.arend.ext.core.ops.CMP
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.module.ModuleLocation
import org.arend.typechecking.implicitargs.equations.DummyEquations
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.coreapi.ArendGoal

/**
 * A proposition field of a record-typed hypothesis brought into the context, `\case d.inv-right \with { | q => {?} }`
 * for `d : LDiv b a`: arend-lib projects such fields all the time (`d.inv-right`, `m|n.inv-right`, `e.f_ret j`) and
 * rewrites, chains or solves with them (`idempotent_LDiv`, `div_mod`, `natAssociates-areEqual`). `\let` bindings are
 * invisible to a goal's context, hence the `\case`. Applies to records, not to class instances (`A : Ring`, whose
 * fields are the axioms the library states as lemmas), and once per field: not when the context already has a
 * hypothesis of the field's type.
 */
class ProjectionGenerator(private val moduleLocation: ModuleLocation, private val cost: Double = 0.4) : ProofStepGenerator<ArendGoal> {
  override fun generate(goal: ArendGoal, currentProof: Proof<ArendGoal>?): List<ProofStep<ArendGoal>> {
    val factory = goal.typechecker.factory
    val context = StepBuilder.context(goal)
    val steps = mutableListOf<ProofStep<ArendGoal>>()
    for ((ref, binding) in context) {
      val classCall = binding.type.normalize(NormalizationMode.WHNF) as? ClassCallExpression ?: continue
      // Records only: a class instance's fields (`A : Ring`, its axioms) are the library's lemmas, not this hypothesis's content
      if (!classCall.definition.isRecord) continue
      for (field in classCall.definition.allFields) {
        if (classCall.isImplemented(field)) continue
        val projection = org.arend.core.expr.FieldCallExpression.make(field, org.arend.core.expr.ReferenceExpression(binding))
        val type = projection.type ?: continue
        if (!LemmaHints.isProposition(type)) continue
        if (context.any { (_, other) -> CompareVisitor.compare(DummyEquations.getInstance(), CMP.EQ, other.type, type, null, null) }) continue
        val term = factory.app(factory.ref(field.ref), listOf(factory.arg(factory.ref(ref), false)))
        // A name the context does not use, so that the hypothesis `q : b * b = b` is not shadowed
        val names = context.map { it.first.refName }.toSet()
        val name = factory.local(generateSequence("q") { "$it'" }.first { it !in names })
        val step = factory.caseExpr(false, listOf(factory.caseArg(term, null, null)), null, null, listOf(factory.clause(listOf(factory.refPattern(name, null)), factory.goal())))
        StepBuilder.build(goal, currentProof, step, cost, moduleLocation)?.let { steps.add(it) }
      }
    }
    return steps
  }
}
