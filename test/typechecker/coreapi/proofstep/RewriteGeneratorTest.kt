package typechecker.coreapi.proofstep

import integration.TestLibrary
import org.arend.core.expr.ReferenceExpression
import org.junit.jupiter.api.Assumptions.assumeTrue
import typechecker.cli.CliProcessApi
import typechecker.coreapi.ArendGoal
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/** Rewriting on goals adapted from arend-lib (`test-lib-std/src/TestRewrite.ard`). */
class RewriteGeneratorTest {
  private object TestRewrite : TestModule("TestRewrite", TestLibrary::loadStd)

  private fun generator(
    premises: List<String> = emptyList(),
    lemmas: List<String> = emptyList(),
    rewriteRetrievers: List<PremiseRetriever> = listOf(FixedPremiseRetriever(lemmas)),
  ): (ArendGoal) -> HeuristicStepGenerator = {
    val module = TestRewrite.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = listOf(FixedPremiseRetriever(premises)),
      heuristics = setOf(Heuristic.CLOSE, Heuristic.APPLY, Heuristic.REWRITE, Heuristic.TRANSPORT),
      rewriteRetrievers = rewriteRetrievers,
    )
  }

  private fun steps(name: String): List<String> = TestRewrite.withGoal(name) { goal ->
    generator()(goal).generate(goal, null).map { it.proof.toString() }
  }

  @Test
  fun `a hypothesis is rewritten with only in the direction that replaces a side of the goal`() {
    // p : 0 = y, goal x < suc y: y occurs, 0 does not
    val proposed = steps("rewriteI-hyp")
    assertTrue("rewriteI p {?}" in proposed && "rewrite p {?}" !in proposed, proposed.toString())
  }

  @Test
  fun `a hypothesis is rewritten in another only when that one mentions the side and has the goal's head`() {
    // p : a = b, h : P b, goal P a: b occurs in h, a does not
    val proposed = steps("rewrite-then-hyp")
    assertTrue("rewriteI p in h" in proposed && "rewrite p in h" !in proposed, proposed.toString())
    // q : x < y has the goal's head but neither x nor y has a part to replace in h; no rewrite of y = y
    val irrelevant = steps("rewrite-irrelevant")
    assertTrue(irrelevant.none { it.startsWith("rewrite") }, irrelevant.toString())
  }

  @Test
  fun `rewrite with a hypothesis, then idp`() {
    TestRewrite.assertProves(TestRewrite.search("rewrite-hyp", generator()), "rewrite p idp")
  }

  @Test
  fun `rewriteI with a hypothesis, then close with another one`() {
    TestRewrite.assertProves(TestRewrite.search("rewriteI-hyp", generator()), "rewriteI p q")
  }

  @Test
  fun `rewrite, then close with a hypothesis`() {
    TestRewrite.assertProves(TestRewrite.search("rewrite-then-hyp", generator()), "rewriteI p in h")
  }

  @Test
  fun `rewrite, then close with a library lemma`() {
    TestRewrite.assertProves(TestRewrite.search("rewrite-then-lemma", generator(premises = listOf("id<suc"))), "rewrite p id<suc")
  }

  @Test
  fun `rewrite with a library equation whose arguments are inferred`() {
    TestRewrite.assertProves(TestRewrite.search("rewrite-comm", generator(lemmas = listOf("NatSemiring.+-comm"))), "rewrite +-comm idp")
  }

  @Test
  fun `a chain of library rewrites`() {
    // The equation solver closes the last step as well
    assertTrue(TestRewrite.assertProves(TestRewrite.search("rewrite-chain", generator(lemmas = listOf("*-assoc", "inverse-left", "ide-left")))) in setOf(
      "rewriteI *-assoc (rewrite inverse-left (rewrite ide-left idp))",
      "rewriteI *-assoc (rewrite inverse-left equation)",
      // The first rewrite may also be a path chain starting with the library equation
      "inv *-assoc *> rewrite inverse-left equation",
      "inv *-assoc *> rewrite inverse-left (rewrite ide-left idp)",
    ))
  }

  @Test
  fun `the same lemma at two places`() {
    TestRewrite.assertProves(TestRewrite.search("rewrite-twice", generator(lemmas = listOf("-'0"))), "rewrite -'0 (rewrite -'0 idp)")
  }

  @Test
  fun `rewrite in a hypothesis`() {
    TestRewrite.assertProves(TestRewrite.search("rewrite-in", generator()), "rewrite p in q")
  }

  @Test
  fun `equations with a bare variable as the rewritten side are not used in that direction`() {
    val lemma = TestRewrite.premises("expand-zero").single()
    assertTrue(RewriteGenerator.lemmaSides(lemma)!!.first is ReferenceExpression)
    val steps = TestRewrite.withGoal("rewrite-hyp") { goal ->
      val module = TestRewrite.module
      val metas = RewriteMetas(TestRewrite.scopeRef("rewrite"), TestRewrite.scopeRef("rewriteI"))
      RewriteGenerator(module.location, metas, listOf(lemma)).generate(goal, null).map { it.proof.toString() }
    }
    assertTrue(steps.none { it.startsWith("rewrite expand-zero") }, "Steps: $steps")
  }

  @Test
  fun `equations are retrieved for the functions of the goal`() {
    // One search for `=` serves every symbol; the equations are matched to the goal's symbols here
    val cli = FakeCli(mapOf("=" to listOf(
      searchResult("ldistr", "x * (y + z) = x * y + x * z"),
      searchResult("+-comm", "x + y = y + x"),
      searchResult("not-an-equation", "x + y <= z"),
      searchResult("takes-an-equation", "(x + y = z) -> P"),
      searchResult("-'0", "n -' 0 = n"),
      searchResult("*-comm", "x * y = y * x"),
    )))
    val candidates = TestRewrite.withGoal("rewrite-twice") { EquationRetriever(cli).retrieve(it) }

    assertEquals(listOf("="), cli.patterns)
    // `ldistr` mentions `*`, which the goal does not; equally good equations of both symbols alternate
    assertEquals(listOf("+-comm" to 1.5, "-'0" to 1.5, "ldistr" to 2.5), candidates.map { it.name to it.cost })
  }

  @Test
  fun `operators are searched by name and recognized by their alias`() {
    // Proof search only knows the field `meet`, but prints it as `∧`
    val libOrder = TestModule("LibOrder", TestLibrary::loadStd)
    val cli = FakeCli(mapOf("=" to listOf(searchResult("meet-comm", "x ∧ y = y ∧ x", "Order.Lattice"))))
    val (head, candidates) = libOrder.withGoal("meet-idemp'") { PremiseRetriever.head(it.expectedType) to EquationRetriever(cli).retrieve(it) }

    assertEquals(Symbol("=", null), head?.copy(alias = null))
    assertEquals(listOf("="), cli.patterns)
    assertEquals(listOf("meet-comm" to EquationRetriever.SIDE_HEAD_COST), candidates.map { it.name to it.cost })
  }

  @Test
  fun `library equations are retrieved by the CLI's proof search`() {
    assumeTrue(TestLibrary.cliJar != null && TestLibrary.arendLibsDir != null, "Arend CLI jar or arend-lib not found")
    val cli = CliProcessApi(TestLibrary.testLibStdDir, TestLibrary.cliJar!!, listOf(TestLibrary.arendLibsDir!!))
    val retriever = EquationRetriever(cli, maxSymbols = 2)
    TestRewrite.assertProves(TestRewrite.search("rewrite-twice", generator(rewriteRetrievers = listOf(retriever))), "rewrite -'0 (rewrite -'0 idp)")
  }

  @Test
  fun `a rewrite is not undone by the same equation the other way`() {
    val (outer, inner) = TestRewrite.withGoal("rewrite-hyp") { goal ->
      val module = TestRewrite.module
      val rewriting = HeuristicStepGenerator(
        module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
        retrievers = emptyList(), heuristics = setOf(Heuristic.REWRITE),
      )
      val outer = rewriting.generate(goal, null)
      val step = outer.first { it.proof.toString() == "rewrite p {?}" }
      // The goal is now `suc y = suc y`, where `y` occurs: `rewriteI p` would be activated, and would undo the rewrite
      val innerGoal = step.proof.goals().single()
      outer.map { it.proof.toString() } to rewriting.generate(innerGoal, step.proof).map { it.proof.toString() }
    }
    assertTrue("rewrite p {?}" in outer, outer.toString())
    assertTrue(inner.none { it.startsWith("rewriteI p") }, inner.toString())
  }

  @Test
  fun `a relation is transported along an equation with a bare-parameter side, which rewrite cannot use`() {
    val module = TestRewrite.module
    fun generator(vararg lemmas: String) = HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = emptyList(), heuristics = setOf(Heuristic.TRANSPORT, Heuristic.REWRITE), rewriteRetrievers = listOf(FixedPremiseRetriever(lemmas.toList())),
      closingMetas = emptyList(),
    )
    val steps = TestRewrite.withGoal("mod<=left'") { goal -> generator("Nat.divModProp").generate(goal, null).map { it.proof.toString() } }
    assertTrue(steps.any { it.startsWith("transport") && it.contains("divModProp n m") }, steps.toString())
    // An equation with two rigid sides is rewritten with, not transported along
    val rigid = TestRewrite.withGoal("rewrite-comm") { goal -> generator("NatSemiring.+-comm").generate(goal, null).map { it.proof.toString() } }
    assertTrue(rigid.none { it.startsWith("transport") } && rigid.any { it.startsWith("rewrite") }, rigid.toString())
  }

  @Test
  fun `transport then linear arithmetic proves the mod bound`() {
    val source = TestRewrite.assertProves(TestRewrite.search("mod<=left'", generator(lemmas = listOf("Nat.divModProp"))))
    assertTrue(source.contains("transport") && source.contains("divModProp n m"), source)
  }
}
