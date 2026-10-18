package typechecker.coreapi.proofstep

import integration.TestLibrary
import typechecker.coreapi.ArendGoal
import kotlin.test.Test
import kotlin.test.assertTrue

/** Splits on stuck `\case` expressions (`mcases`) and compound expressions, on `test-lib-std/src/TestMCases.ard`. */
class MCasesTest {
  private object TestMCases : TestModule("TestMCases", TestLibrary::loadStd)

  private fun generator(premises: List<String>, heuristics: Set<Heuristic>, solvers: Boolean): (ArendGoal) -> HeuristicStepGenerator = {
    val module = TestMCases.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = listOf(FixedPremiseRetriever(premises)), splitters = emptyList(), heuristics = heuristics,
      closingMetas = if (solvers) HeuristicStepGenerator.DEFAULT_CLOSING_METAS else HeuristicStepGenerator.BASIC_CLOSING_METAS,
    )
  }

  private fun search(name: String, vararg premises: String, heuristics: Set<Heuristic> = Heuristic.entries.toSet(), solvers: Boolean = true, maxExpansions: Int = 300) =
    TestMCases.search(name, generator(premises.toList(), heuristics, solvers), maxExpansions = maxExpansions, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)

  @Test
  fun `mcases on the case expression the goal computes to`() {
    // Splitting `a` first is also accepted: `decideEq (suc a) (suc a)` is then settled by mcases one level down
    val source = TestMCases.assertProves(search("eqCount-self"))
    assertTrue(source.contains("mcases {1} () (\\case  \\with {  | yes p => idp  | no p => contradiction})"), source)
  }

  @Test
  fun `mcases on the inner of two calls of a function`() {
    TestMCases.assertProves(search("notb-notb"), "mcases {(notb, 2)} () (\\case  \\with {  | false => idp  | true => idp})")
  }

  @Test
  fun `split on a compound expression, refuting a branch by applying a hypothesis`() {
    // linarith refutes the branch as well; this is about applying the hypothesis
    val source = TestMCases.assertProves(search("pos_iabs'", "NatSemiring.triLess", solvers = false))
    // triLess needs `neg (suc d)`, so the neg branch splits its argument once more
    assertTrue(source.contains("\\case x - y \\as x', idp : x - y = x' \\with") && source.contains("absurd (y<=x (triLess p))"), source)
  }

  @Test
  fun `split on a compound expression keeping the equation`() {
    // Without induction, which proves it by splitting n and m and recursing
    val source = TestMCases.assertProves(search("minus-zero-or-pos", "byLeft", "byRight", "zero<suc", heuristics = Heuristic.entries.toSet() - Heuristic.INDUCTION, maxExpansions = 800))
    // In the first branch the equation `p : n -' m = 0` is the disjunct itself
    assertTrue(source.contains("\\case n -' m \\as x, idp : n -' m = x \\with") && source.contains("byLeft p"), source)
  }
}
