package typechecker.coreapi.proofstep

import integration.TestLibrary
import org.junit.jupiter.api.Assumptions.assumeTrue
import typechecker.cli.CliApi
import typechecker.cli.CliProcessApi
import typechecker.cli.ProofSearchResponse
import typechecker.cli.SearchResult
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.proofstep.TestAppModule.assertProves
import typechecker.coreapi.proofstep.TestAppModule.module
import typechecker.coreapi.proofstep.TestAppModule.search
import typechecker.coreapi.proofstep.TestAppModule.withGoal
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.test.assertTrue

class HeuristicStepGeneratorTest {

  companion object {
    /** Shared, so its cache of CLI results is reused across tests. */
    private val cliRetriever: ProofSearchRetriever by lazy { ProofSearchRetriever(CliProcessApi(TestLibrary.testLibDir, TestLibrary.cliJar!!)) }

    private fun requireCliRetriever(): ProofSearchRetriever {
      assumeTrue(TestLibrary.cliJar != null, "Arend CLI jar not found; set -Darend.jar")
      return cliRetriever
    }
  }

  private fun result(name: String, expression: String, module: String = "TestApp") =
    SearchResult(module = module, name = name, kind = "LEMMA", expression = expression)

  private fun heuristicGenerator(vararg retrievers: PremiseRetriever): (ArendGoal) -> HeuristicStepGenerator = {
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server,
      module.libraryName, module.location.modulePath, retrievers.toList(), heuristics = setOf(Heuristic.APPLY)
    )
  }

  // ── Goal heads and slices ──────────────────────────────────────

  @Test
  fun `head of a goal looks through applications and function types`() {
    assertEquals("Pos", withGoal("app-implicit") { PremiseRetriever.headName(it.expectedType) })
    assertEquals("PosPair", withGoal("app-telescope") { PremiseRetriever.headName(it.expectedType) })
    assertEquals("Q", withGoal("app-pi") { PremiseRetriever.headName(it.expectedType) })
  }

  @Test
  fun `slices are split only at top-level spaces`() {
    assertEquals(listOf("(Pos x)", "->", "PosPair", "x", "y"), ProofSearchRetriever.topLevelTokens("(Pos x) -> PosPair x y"))
    assertEquals(listOf("f", "{A}", "(g x)"), ProofSearchRetriever.topLevelTokens("f {A} (g x)"))
  }

  @Test
  fun `codomains are ranked by where the goal head occurs`() {
    fun cost(codomain: String, head: String) = ProofSearchRetriever.codomainCost(ProofSearchRetriever.topLevelTokens(codomain), head)
    assertEquals(ProofSearchRetriever.HEAD_COST, cost("Pos (suc n)", "Pos"))
    assertEquals(ProofSearchRetriever.HEAD_COST, cost("Order.<= x y", "<="))
    assertEquals(ProofSearchRetriever.HEAD_COST, cost("n < m", "<"))
    assertEquals(ProofSearchRetriever.TOP_LEVEL_COST, cost("a + b = c", "="))
    assertEquals(ProofSearchRetriever.NESTED_COST, cost("Q (Pos n)", "Pos"))
    assertNull(cost("Q n", "Pos"))
  }

  @Test
  fun `constructors of the goal's data type are retrieved without search`() {
    val candidates = withGoal("app-implicit") { ConstructorRetriever().retrieve(it) }
    assertEquals(listOf("Pos.pos-one-con", "Pos.pos-suc-con"), candidates.map { it.name })
    assertTrue(candidates.all { it.module == "TestApp" })
  }

  // ── ProofSearchRetriever ranking (canned CLI results) ──────────

  @Test
  fun `retriever ranks matches by where the head occurs in the codomain`() {
    val cli = FakeCli(mapOf("Pos" to listOf(
      result("pos-pair", "(Pos x) -> PosPair x y"),
      result("nested", "Q (Pos n)"),
      result("pos-succ", "Pos (suc n)"),
      result("pos-one", "Pos 1"),
    )))
    val candidates = withGoal("app-implicit") { ProofSearchRetriever(cli).retrieve(it) }

    assertEquals(listOf("Pos"), cli.patterns)
    // pos-pair only takes a Pos: its codomain `PosPair x y` does not mention Pos (PosPair is another name)
    assertEquals(listOf("pos-succ", "pos-one", "nested"), candidates.map { it.name })
    assertEquals(listOf(1.0, 1.0, 2.0), candidates.map { it.cost })
    assertTrue(candidates.all { it.module == "TestApp" })
  }

  @Test
  fun `retriever prefers premises that take a hypothesis of the goal`() {
    // Full signatures, as the index asks for: r-lem takes a Q, which the goal has as a hypothesis
    val cli = FakeCli(mapOf("R" to listOf(
      SearchResult(module = "TestApp", name = "r-other", kind = "LEMMA", signature = "\\lemma r-other : R"),
      SearchResult(module = "TestApp", name = "r-lem", kind = "LEMMA", signature = "\\lemma r-lem (q : Q) : R"),
    )))
    val candidates = withGoal("app-hypothesis") { ProofSearchRetriever(cli).retrieve(it) }

    assertEquals(listOf("R"), cli.patterns)
    assertEquals(listOf("r-lem" to ProofSearchRetriever.HEAD_COST - ProofSearchRetriever.HYPOTHESIS_BONUS, "r-other" to 1.0), candidates.map { it.name to it.cost })
  }

  @Test
  fun `retriever caps the number of candidates`() {
    val cli = FakeCli(mapOf("Pos" to (1..10).map { result("lemma$it", "Pos $it") }))
    val candidates = withGoal("app-implicit") { ProofSearchRetriever(cli, maxCandidates = 3).retrieve(it) }
    assertEquals(listOf("lemma1", "lemma2", "lemma3"), candidates.map { it.name })
  }

  @Test
  fun `retriever survives a failing CLI`() {
    val cli = object : CliApi by FakeCli(emptyMap()) {
      override fun proofSearch(pattern: String): ProofSearchResponse = throw java.io.IOException("CLI is down")
    }
    assertEquals(emptyList(), withGoal("app-implicit") { ProofSearchRetriever(cli).retrieve(it) })
  }

  // ── Premise resolution ─────────────────────────────────────────

  @Test
  fun `unfinished definitions and unknown names are not used as premises`() {
    val premises = withGoal("app-implicit") { goal ->
      heuristicGenerator()(goal).resolvePremises(goal, listOf(
        PremiseCandidate("app-unprovable", "TestApp"),  // has a goal
        PremiseCandidate("app-implicit", "TestApp"),    // the definition being proved
        PremiseCandidate("no-such-lemma", "TestApp"),
        PremiseCandidate("pos-succ", "TestApp", 1.5),
        PremiseCandidate("pos-one"),
      ))
    }
    assertEquals(listOf("pos-one" to 1.0, "pos-succ" to 1.5), premises.map { (def, cost) -> def.name to cost })
  }

  @Test
  fun `fixed premises still drive the search`() {
    assertProves(search("app-two", heuristicGenerator(FixedPremiseRetriever(listOf("q-lem", "p-lem")))), "q-lem p-lem")
  }

  // ── Search with premises retrieved by the CLI's -ps ────────────

  @Test
  fun `CLI proof search retrieves the lemmas concluding the goal`() {
    val retriever = requireCliRetriever()
    val names = withGoal("app-implicit") { retriever.retrieve(it) }.map { it.name }
    assertTrue("pos-succ" in names && "pos-one" in names, "Should retrieve pos-succ and pos-one: $names")
    assertTrue("pos-pair" !in names, "pos-pair only takes a Pos, it does not conclude one: $names")
  }

  @Test
  fun `CLI proof search ranks premises taking a hypothesis first`() {
    val retriever = requireCliRetriever()
    val candidates = withGoal("app-hypothesis") { retriever.retrieve(it) }
    // Both the lemma and the constructor take the hypothesis's Q
    val takingQ = candidates.filter { it.cost == ProofSearchRetriever.HEAD_COST - ProofSearchRetriever.HYPOTHESIS_BONUS }.map { it.name }
    assertTrue("r-lem" in takingQ && "R.r-con" in takingQ, "Candidates: $candidates")
    assertEquals(takingQ.toSet(), candidates.take(takingQ.size).map { it.name }.toSet(), "Candidates: $candidates")
  }

  @Test
  fun `search with retrieved premises chains several applications`() {
    val retriever = requireCliRetriever()
    // Constructors are retrieved too, and the CLI lists them before the lemmas defined after them
    assertProves(search("app-two", heuristicGenerator(retriever)), "q-con p-con")
    assertProves(search("app-branching", heuristicGenerator(retriever)), "r-con p-con (q-con p-con)")
    assertProves(search("app-implicit", heuristicGenerator(retriever)), "pos-succ (pos-succ pos-one)")
    // The constructor and the lemma cost the same
    assertTrue(assertProves(search("app-telescope", heuristicGenerator(retriever))) in setOf("pos-pair-con pos-one (pos-succ pos-one)", "pos-pair _ _ pos-one (pos-succ pos-one)"))
    // Either the hypothesis q itself or a proof of Q fills r-con's second argument; the tie is not stable
    assertTrue(assertProves(search("app-hypothesis", heuristicGenerator(retriever))) in setOf("r-con p-con q", "r-con p-con (q-con p-con)"))
  }

  @Test
  fun `search with retrieved premises does not use unfinished lemmas`() {
    // app-unprovable itself concludes Pos 0, but it is the goal being proved
    assertNull(search("app-unprovable", heuristicGenerator(requireCliRetriever())).proof)
  }
}
