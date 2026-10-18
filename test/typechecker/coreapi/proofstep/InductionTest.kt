package typechecker.coreapi.proofstep

import integration.TestLibrary
import typechecker.coreapi.ArendGoal
import kotlin.test.Test
import kotlin.test.assertNull
import kotlin.test.assertTrue

/** Proofs by induction on `test-lib-std/src/TestInduction.ard`: a recursive call inside a `\case \elim` branch. */
class InductionTest {
  private object TestInduction : TestModule("TestInduction", TestLibrary::loadStd)

  private fun generator(vararg premises: String): (ArendGoal) -> HeuristicStepGenerator = {
    val module = TestInduction.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = listOf(FixedPremiseRetriever(premises.toList())), splitters = emptyList(),
      // linarith would prove id<suc outright; these tests are about the recursive call
      closingMetas = HeuristicStepGenerator.BASIC_CLOSING_METAS,
    )
  }

  private fun search(name: String, vararg premises: String) =
    TestInduction.search(name, generator(*premises), maxExpansions = 300, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
      .also { result -> result.proof?.let { println("SOURCE $name ${it.toSource()}") } }

  @Test
  fun `recursive call closes the inductive step`() {
    TestInduction.assertProves(search("-'+'", "-'0"), "\\case \\elim m \\with {\n  | zero => -'0\n  | suc m => -'+'\n}")
  }

  @Test
  fun `recursive call under a constructor`() {
    TestInduction.assertProves(search("id<suc'", "zero<suc", "suc<suc"), "\\case \\elim n \\with {\n  | zero => zero<suc\n  | suc n => suc<suc id<suc'\n}")
  }

  @Test
  fun `recursive call under pmap`() {
    TestInduction.assertProves(search("length_++'"), "\\case \\elim l \\with {\n  | nil => idp\n  | x :: l => pmap suc length_++'\n}")
  }

  @Test
  fun `the inductive step rewrites with the induction hypothesis`() {
    val source = TestInduction.assertProves(search("pow_+'", "ide-right", "*-assoc"))
    assertTrue(source.contains("rewrite (pow_+' {_} {_} {_} {m})"), source)
  }

  @Test
  fun `a recursive call that does not decrease is not proposed`() {
    // cancel-right needs `pmap pred p` for the hypothesis; a plain `cancel-right' k` would recurse on k itself
    val result = search("cancel-right'", "pred")
    result.proof?.let { TestInduction.assertProves(result) }
  }

  @Test
  fun `the inductive step chains the induction hypothesis with a transitivity operator`() {
    val module = TestInduction.module
    val solving = { goal: ArendGoal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(),
      )
    }
    val source = TestInduction.assertProves(TestInduction.search("-'<=id'", solving, maxExpansions = 400, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20))
    assertTrue(Regex("-'<=id'[^<]*<=∘|<=∘ -'<=id'").containsMatchIn(source), source)
  }

  @Test
  fun `a proof introducing the negated equation is printed with the lambda inside the clauses`() {
    val module = TestInduction.module
    val solving = { goal: ArendGoal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), destructorRetrievers = listOf(FixedPremiseRetriever(listOf("pred"))),
      )
    }
    val result = TestInduction.search("id/=suc'", solving, maxExpansions = 400, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
    TestInduction.assertProves(result)
    val source = (result.proof as typechecker.coreapi.ArendProof).toSource()
    assertTrue(source.startsWith("\\elim n") && source.contains("=> \\lam p => ") && source.contains("id/=suc' {n}"), source)
  }

  @Test
  fun `the inductive step is given to the monoid solver with the induction hypothesis as a hint`() {
    val module = TestInduction.module
    val solving = { goal: ArendGoal ->
      HeuristicStepGenerator(module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath, retrievers = emptyList(), splitters = emptyList())
    }
    val result = TestInduction.search("pow-comm1'", solving, maxExpansions = 400, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
    val source = TestInduction.assertProves(result)
    assertTrue(source.contains("monoid {(p, pow-comm1'"), source)
  }

  @Test
  fun `the solver takes lemma instances as hints besides the induction hypothesis`() {
    val module = TestInduction.module
    val solving = { goal: ArendGoal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("Monoid.pow-comm1"))),
      )
    }
    val result = TestInduction.search("pow-comm'", solving, maxExpansions = 400, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
    val source = TestInduction.assertProves(result)
    assertTrue(source.contains("monoid {(pow-comm' {A} {a} {b} p {n}, pow-comm1 (inv p))}"), source)
  }

  @Test
  fun `lemma instances are lemmas applied to hypotheses shaped like their parameters`() {
    val module = TestInduction.module
    val generator = HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = emptyList(), splitters = emptyList(), rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("Monoid.pow-comm1", "Monoid.pow_+"))),
    )
    // `p : a * b = b * a` is what pow-comm1 asks for, directly and reversed; pow_+ asks for no proposition
    val hints = TestInduction.withGoal("pow-comm-hint'") { generator.lemmaHints(it).map { hint -> hint.toString() } }
    assertTrue(hints.toSet() == setOf("pow-comm1 p", "pow-comm1 (inv p)"), hints.toString())
    // `q : a = b` is not shaped like `a * b = b * a`: nothing is offered
    val none = TestInduction.withGoal("no-hint'") { generator.lemmaHints(it).map { hint -> hint.toString() } }
    assertTrue(none.isEmpty(), none.toString())
    // The hinted solver closes the goal
    val source = TestInduction.assertProves(TestInduction.search("pow-comm-hint'", { generator }, maxExpansions = 50))
    assertTrue(source.contains("monoid {pow-comm1 p}"), source)
  }

  @Test
  fun `congruence through a class operation and the fit_BigSum induction`() {
    val module = TestInduction.module
    val steps = TestInduction.withGoal("cong-field'") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.CONGRUENCE), closingMetas = emptyList(),
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue(steps.any { it.startsWith("pmap (") && it.contains("a + z") || it.contains("a +") }, steps.toString())
    // `BigSum (fit zro {suc n} nil) = BigSum nil` is `rewrite BigSum_replicate0` then `idp`; the cons case is the library's
    // `pmap (a +) $ fit_BigSum \lam j n<=j => p (suc j) (suc<=suc n<=j)`
    val searching = { _: ArendGoal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = listOf(FixedPremiseRetriever(listOf("AddMonoid.BigSum_zro", "suc<=suc", "zero<=_"))), splitters = emptyList(),
        rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("AddMonoid.BigSum_replicate0"))), closingMetas = HeuristicStepGenerator.BASIC_CLOSING_METAS,
      )
    }
    val result = TestInduction.search("fit_BigSum'", searching, maxExpansions = 600, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
    val source = TestInduction.assertProves(result)
    assertTrue(source.contains("(fit_BigSum' (\\lam j => \\lam p' => p (suc j) (suc<=suc p')))"), source)
  }

  @Test
  fun `a chain ends with the hypothesis function applied, its argument inferred from the goal`() {
    val module = TestInduction.module
    val chaining = { _: ArendGoal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = listOf(FixedPremiseRetriever(listOf("suc<=suc", "zero<=_"))), splitters = emptyList(), closingMetas = HeuristicStepGenerator.BASIC_CLOSING_METAS,
      )
    }
    // At the top, `n <= f n`, no end of `mon _ : suc (f _) <= f (suc _)` matches: the chain appears in the `suc n` case
    val steps = TestInduction.withGoal("monotone-diagonal'") { goal -> chaining(goal).generate(goal, null).map { it.proof.toString() } }
    assertTrue(steps.none { it.contains("mon ") }, steps.toString())
    val source = TestInduction.assertProves(TestInduction.search("monotone-diagonal'", chaining, maxExpansions = 600, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20))
    // The chain writes its middle term: `suc<=suc IH <=∘ {_} {_} {suc (f n)} {_} mon n`
    assertTrue(source.contains("suc<=suc (monotone-diagonal' _ mon") && source.contains("<=∘ {_} {_} {suc (f n)} {_} mon n"), source)
  }
}
