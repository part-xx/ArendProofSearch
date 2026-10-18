package typechecker.coreapi.proofstep

import integration.TestLibrary
import typechecker.coreapi.ArendGoal
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/** Case analysis on goals adapted from arend-lib (`test-lib-std/src/TestCase.ard`). */
class CaseGeneratorTest {
  private object TestCase : TestModule("TestCase", TestLibrary::loadStd)

  private fun generator(
    vararg premises: String,
    heuristics: Set<Heuristic> = Heuristic.entries.toSet(),
  ): (ArendGoal) -> HeuristicStepGenerator = {
    val module = TestCase.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = listOf(FixedPremiseRetriever(premises.toList())), heuristics = heuristics,
    )
  }

  private fun caseSteps(defName: String): List<String> = TestCase.withGoal(defName) { goal ->
    val module = TestCase.module
    CaseGenerator(module.location).generate(goal, null).map { it.proof.toString() }
  }

  @Test
  fun `split a Bool variable of the goal`() {
    TestCase.assertProves(TestCase.search("not-not", generator()), "\\case \\elim b \\with {\n  | false => idp\n  | true => idp\n}")
  }

  @Test
  fun `split a Nat variable of the goal`() {
    TestCase.assertProves(TestCase.search("minus-zero", generator()), "\\case \\elim n \\with {\n  | zero => idp\n  | suc n => idp\n}")
  }

  @Test
  fun `hypotheses depending on the variable are eliminated with it`() {
    TestCase.assertProves(
      TestCase.search("suc-pred", generator()),
      "\\case \\elim n, \\elim n/=0 \\with {\n  | zero, n/=0 => contradiction\n  | suc n, n/=0 => idp\n}"
    )
  }

  @Test
  fun `split a disjunction hypothesis`() {
    TestCase.assertProves(
      TestCase.search("or-symm", generator("byLeft", "byRight")),
      "\\case h \\with {\n  | byLeft p => byRight p\n  | byRight p' => byLeft p'\n}"
    )
  }

  @Test
  fun `split an array into nil and cons`() {
    val source = TestCase.assertProves(TestCase.search("big-meet-left", generator("<=-refl", "meet-right", "<=-transitive"), maxExpansions = 300, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20))
    assertTrue(source.contains("| a :: l => meet-right <=∘"), source)
  }

  @Test
  fun `an array of a variable length is split together with its length`() {
    val steps = caseSteps("array-ext")
    assertTrue(steps.any { it.contains("| 0, nil, l', p => {?}") && it.contains("| suc n, a :: l, l', p => {?}") }, steps.toString())
  }

  @Test
  fun `a hypothesis whose type is a type definition is split through its unfolding`() {
    val steps = caseSteps("tsetim-elim")
    assertTrue(steps.any { it.contains("| inP (a, p) => {?}") }, steps.toString())
  }

  @Test
  fun `split an existential with a tuple pattern`() {
    TestCase.assertProves(TestCase.search("exists-snd", generator()), "\\case h \\with {\n  | inP (a, p) => p\n}")
  }

  @Test
  fun `split on trichotomy of two elements`() {
    TestCase.assertProves(
      TestCase.search("lt-of-le-ne", generator()),
      // arend-lib splits on trichotomy; deciding the hypothesis `p : a <= a'` is one branch shorter
      "\\case <=-dec p \\with {\n  | inl p' => p'\n  | inr p'' => contradiction\n}"
    )
  }

  @Test
  fun `split on decideEq of two elements`() {
    TestCase.assertProves(
      TestCase.search("tightness'", generator()),
      "\\case decideEq x y \\with {\n  | yes p => p\n  | no p' => contradiction\n}"
    )
  }

  @Test
  fun `an equation between different constructors is refuted by an empty case`() {
    TestCase.assertProves(TestCase.search("suc/=0'", generator(heuristics = setOf(Heuristic.CASE))), "\\case p \\with {}")
    // contradiction finds the refutation too, and closing steps are tried first
    TestCase.assertProves(TestCase.search("suc/=0'", generator()), "contradiction")
  }

  @Test
  fun `a hypothesis of an empty type is refuted by an empty case`() {
    TestCase.assertProves(TestCase.search("fin0-elim", generator(heuristics = setOf(Heuristic.CASE))), "\\case i \\with {}")
  }

  @Test
  fun `split on meet-isMin and rewrite with the branch equation`() {
    // arend-lib rewrites the goal (`rewrite p ha`); rewriting the hypothesis takes one step less
    TestCase.assertProves(
      TestCase.search("meet-pred", generator()),
      "\\case meet-isMin a b \\with {\n  | byLeft p => rewriteI p in ha\n  | byRight p' => rewriteI p' in hb\n}"
    )
  }

  @Test
  fun `a negated goal is refuted outright, as fsuc-not-zero`() {
    // Data/Fin.ard:23 fsuc/=0: \case __ ; contradiction handles the `Not` itself
    TestCase.assertProves(TestCase.search("fsuc/=0'", generator()), "contradiction")
  }

  @Test
  fun `a goal of a function type is introduced`() {
    TestCase.assertProves(TestCase.search("intro-hyp", generator()), "\\lam x => p")
  }

  @Test
  fun `a recursive variable that occurs nowhere is not split`() {
    val steps = caseSteps("no-split-unused")
    assertTrue(steps.none { it.contains("\\case n ") || it.contains("\\elim n") }, "Steps: $steps")
    assertTrue(steps.any { it.startsWith("\\case \\elim b") }, "Steps: $steps")
  }

  @Test
  fun `a proposition is not eliminated into a non-propositional goal`() {
    assertEquals(emptyList(), caseSteps("no-split-trunc"))
  }

  @Test
  fun `a function hypothesis is applied to a constructor of a variable when a hole cannot be inferred`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("tail-bound") { HypothesisGenerator(module.location).generate(it, null).map { step -> step.proof.toString() } }
    assertTrue("f (suc i)" in steps, steps.toString())
  }

  @Test
  fun `a function hypothesis is applied to a nullary constructor`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("head-bound") { HypothesisGenerator(module.location).generate(it, null).map { step -> step.proof.toString() } }
    assertTrue("f 0" in steps || "f zero" in steps, steps.toString())
  }

  @Test
  fun `a field of a concrete instance applied to a variable is stuck on it`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("cons-at-stuck") { CaseGenerator(module.location).generate(it, null) }
    val split = steps.find { it.proof.toString().startsWith("\\case \\elim i") }
    assertTrue(split != null && split.score < CaseGenerator.VARIABLE_COST, steps.map { "${it.score} ${it.proof}" }.toString())
  }

  @Test
  fun `a hypothesis between applications of one head is mapped over a destructor, other hypotheses are not`() {
    val module = TestCase.module
    fun steps(name: String) = TestCase.withGoal(name) { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.INJECTIVITY), closingMetas = emptyList(),
        destructorRetrievers = listOf(FixedPremiseRetriever(listOf("pred"))),
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue("pmap pred p" in steps("unsuc'"), steps("unsuc'").toString())
    assertTrue(steps("unsuc-no").isEmpty(), steps("unsuc-no").toString())
  }

  @Test
  fun `a mapped hypothesis is kept as a new hypothesis when it does not close the goal`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("unsuc-forward") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.INJECTIVITY), closingMetas = emptyList(),
        destructorRetrievers = listOf(FixedPremiseRetriever(listOf("pred"))),
      ).generate(goal, null).map { it.proof.toString().replace("\n", " ") }
    }
    assertTrue(steps.any { it.startsWith("\\case pmap pred p \\with") }, steps.toString())
  }

  @Test
  fun `an equation between different constructors through a coercion is absurd`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("fin-absurd") { CaseGenerator(module.location).generate(it, null).map { step -> step.proof.toString().replace("\n", " ") } }
    assertTrue(steps.any { it.startsWith("\\case p \\with") }, steps.toString())
  }

  @Test
  fun `a lemma concluding a negation is applied to the hypothesis the negation takes`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("not-apply") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = listOf(FixedPremiseRetriever(listOf("id/=suc"))), splitters = emptyList(), heuristics = setOf(Heuristic.APPLY), closingMetas = emptyList(),
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue("id/=suc q" in steps, steps.toString())
  }

  @Test
  fun `congruence over a constructor of Fin uses a lambda, and a Nat equation of Fin elements has Nat destructors`() {
    val module = TestCase.module
    val steps = TestCase.withGoal("fin-suc-cong") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.CONGRUENCE), closingMetas = emptyList(),
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue(steps.any { it.startsWith("pmap (\\lam") && it.contains("=> suc z)") }, steps.toString())
    // `p : suc n = suc m` is an equation in Nat between applications of `suc`; `p : x = y` between bare variables has nothing to peel
    val shapes = TestCase.withGoal("unsuc'") { DestructorRetriever.shapes(it).map { (side, goalType) -> side.name to goalType?.name } }
    assertTrue(("Nat" to "Nat") in shapes, shapes.toString())
    assertTrue(TestCase.withGoal("fin-dep") { DestructorRetriever.shapes(it) }.isEmpty())
  }
}
