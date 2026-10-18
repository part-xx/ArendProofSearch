package typechecker.coreapi.proofstep

import integration.TestLibrary
import typechecker.coreapi.ArendGoal
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/** Path chains, pairs, the solvers and unfolding, on `test-lib-std/src/TestChains.ard`. */
class ChainsTest {
  private object TestChains : TestModule("TestChains", TestLibrary::loadStd)

  private fun generator(premises: List<String>, solvers: Boolean): (ArendGoal) -> HeuristicStepGenerator = {
    val module = TestChains.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = listOf(FixedPremiseRetriever(premises)), splitters = emptyList(),
      closingMetas = if (solvers) HeuristicStepGenerator.DEFAULT_CLOSING_METAS else HeuristicStepGenerator.BASIC_CLOSING_METAS,
    )
  }

  private fun search(name: String, vararg premises: String, solvers: Boolean = true) =
    TestChains.search(name, generator(premises.toList(), solvers), maxExpansions = 300, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)

  @Test
  fun `transitivity chains hypotheses`() {
    // equation would prove it too; this is about chaining
    // rewriting with p and q is as short as chaining them
    assertTrue(TestChains.assertProves(search("trans3", solvers = false)) in setOf("p *> (q *> r)", "rewrite p (rewriteI q in r)"))
  }

  @Test
  fun `a pair of hypotheses`() {
    TestChains.assertProves(search("both"), "(a, b)")
  }

  @Test
  fun `the equation solver closes a monoid identity`() {
    TestChains.assertProves(search("assoc3"), "equation")
  }

  @Test
  fun `linear arithmetic closes an inequality`() {
    TestChains.assertProves(search("lin1"), "linarith")
  }

  @Test
  fun `unfold exposes the case to split, as in dec-less-reduce`() {
    // Splitting on `dec<_<= a a'` itself, keeping the equation, needs no unfolding; unfold + mcases is the library's way
    val source = TestChains.assertProves(search("dec<_reduce'", "prop-pi"))
    val expected = setOf(
      "unfold dec<_<= (mcases {1} () (\\case  \\with {  | less p' => pmap inl prop-pi  | equals p' => contradiction  | greater p' => contradiction}))",
      "\\case dec<_<= {_} a a' \\as x, idp : dec<_<= {_} a a' = x \\with {\n  | inl p', p'' => rewrite p'' (pmap inl prop-pi)\n  | inr p', p'' => contradiction\n}",
    )
    assertTrue(source in expected, source)
  }

  @Test
  fun `a chain starts with a library equation whose side matches the goal's left end`() {
    // Without rewriting, which would prove it as well: the chain `L *> {?}` has to come from the path heuristic
    val module = TestChains.module
    val generator: (ArendGoal) -> HeuristicStepGenerator = {
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = listOf(FixedPremiseRetriever(listOf("Monoid.ide-right"))), rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("Monoid.ide-right"))),
        heuristics = setOf(Heuristic.CLOSE, Heuristic.APPLY), closingMetas = HeuristicStepGenerator.BASIC_CLOSING_METAS,
      )
    }
    TestChains.assertProves(TestChains.search("chain-lemma", generator, maxExpansions = 100, focusFirstGoal = true, openGoalCost = 1.0), "ide-right *> ide-right")
  }

  @Test
  fun `a goal about a function is split on the lemma characterizing it, not on an equation about it`() {
    val module = TestChains.module
    fun steps(vararg lemmas: String) = TestChains.withGoal("finsum-zro") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.CASE), closingMetas = emptyList(),
        splitRetrievers = listOf(FixedPremiseRetriever(lemmas.toList())),
      ).generate(goal, null).map { it.proof.toString().replace("\n", " ") }
    }
    val withCharacterization = steps("AbMonoid.FinSum_char")
    assertTrue(withCharacterization.any { it.startsWith("\\case FinSum_char x \\with") }, withCharacterization.toString())
    // FinSum_char2 concludes an equation: it is applied, not split on
    val withEquation = steps("AbMonoid.FinSum_char2")
    assertTrue(withEquation.none { it.startsWith("\\case") }, withEquation.toString())
  }

  @Test
  fun `a hypothesis's form is brought to the goal by transport along an equation about the hypothesis's function`() {
    val module = TestChains.module
    val steps = TestChains.withGoal("negative_<=-conv'") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.TRANSPORT), closingMetas = emptyList(),
        rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("AddGroup.negative-isInv"))),
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue(steps.any { it.startsWith("transport") && it.contains("negative-isInv") }, steps.toString())
  }

  @Test
  fun `after transporting one side, the other side is transported too`() {
    val module = TestChains.module
    val (first, second) = TestChains.withGoal("negative_<=-conv'") { goal ->
      val transporting = HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.TRANSPORT), closingMetas = emptyList(),
        rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("AddGroup.negative-isInv"))),
      )
      val first = transporting.generate(goal, null)
      val step = first.first { it.proof.toString().startsWith("transport (\\lam z => z") }
      val inner = step.proof.goals().single()
      first.map { it.proof.toString() } to transporting.generate(inner, step.proof).map { it.proof.toString() }
    }
    assertTrue(second.any { it.contains("(\\lam z => negative") }, "first: $first\nsecond: $second")
  }

  @Test
  fun `the group solver takes a hint derived from the hypothesis`() {
    // The sub-meta prints by its own name here; `ArendProof.qualifiedSource` writes `equation.group`
    val sym = TestChains.assertProves(search("comm_sym'"))
    assertTrue(sym.contains("group {pmap inverse p}"), sym)
    val conjugate = TestChains.assertProves(search("comm_conjugate'"))
    assertTrue(conjugate.contains("group {pmap (\\lam z => z * h) p}"), conjugate)
  }

  @Test
  fun `a lemma of the twin structure is applied with the converted instance`() {
    val cli = try { typechecker.cli.CliConnection(TestLibrary.testLibStdDir) } catch (e: Exception) { org.junit.jupiter.api.Assumptions.assumeTrue(false, "needs the daemon: ${e.message}"); return }
    val index = SignatureIndex(cli)
    val module = TestChains.module
    val steps = TestChains.withGoal("inverse-isInv'") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), splitters = emptyList(), heuristics = setOf(Heuristic.APPLY), closingMetas = emptyList(),
        transferRetrieverFactory = { conversions -> TransferRetriever(index, conversions) },
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue(steps.any { it.contains("negative-isInv {fromGroup A}") }, steps.toString())
  }

  @Test
  fun `a premise whose class instance cannot be inferred is applied with the converted instance`() {
    val module = TestChains.module
    val steps = TestChains.withGoal("cancel-left'") { goal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = listOf(FixedPremiseRetriever(listOf("CancelMonoid.cancel_*-left"))), splitters = emptyList(), heuristics = setOf(Heuristic.APPLY), closingMetas = emptyList(),
      ).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue(steps.any { it.contains("cancel_*-left {toGroup A}") && it.endsWith(" p") }, steps.toString())
  }

  @Test
  fun `a relation lemma applied to the hypothesis is brought to the goal by transport2`() {
    val module = TestChains.module
    val generator = { heuristics: Set<Heuristic> ->
      { _: ArendGoal ->
        HeuristicStepGenerator(
          module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
          retrievers = listOf(FixedPremiseRetriever(listOf("PosetAddMonoid.<=_+", "Preorder.<=-refl"))), splitters = emptyList(), heuristics = heuristics,
        )
      }
    }
    val source = TestChains.assertProves(TestChains.search("<=_+-positive'", generator(Heuristic.entries.toSet()), maxExpansions = 300, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20))
    assertTrue(source.contains("transport2 (<=)") && source.contains("(<=_+ a>=0 b>=0)"), source)
    // `<=_+` is about `+`, which neither the goal `y <= z` nor the hypothesis mentions
    val none = TestChains.withGoal("fix-none'") { goal -> generator(setOf(Heuristic.TRANSPORT))(goal).generate(goal, null).map { it.proof.toString() } }
    assertTrue(none.none { it.contains("transport2") }, none.toString())
  }

  @Test
  fun `hypotheses that are functions into equations hint the solver applied to the element at hand`() {
    val source = TestChains.assertProves(search("IsCentral_*'"))
    // The solver rewrites with the hints in order: `y * y'` is a subword of `x * y * y'`, `x * y'` only after it
    assertEquals("\\lam y' => monoid {(yc y', xc y')}", source)
  }

  @Test
  fun `a chain ends with a library lemma whose hypothesis is left as a goal`() {
    val module = TestChains.module
    val chaining = { _: ArendGoal ->
      HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = listOf(FixedPremiseRetriever(listOf("mod_<", "suc<suc", "fin_nat-inj"))), rewriteRetrievers = listOf(FixedPremiseRetriever(listOf("mod_<"))),
        splitters = emptyList(), closingMetas = HeuristicStepGenerator.BASIC_CLOSING_METAS,
      )
    }
    val source = TestChains.assertProves(TestChains.search("mod_suc'", chaining, maxExpansions = 600, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20))
    assertTrue(source.contains("inv (mod_< (suc<suc p))") && source.contains("pmap suc (mod_< p)"), source)
  }
}
