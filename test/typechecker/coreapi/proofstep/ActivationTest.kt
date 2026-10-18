package typechecker.coreapi.proofstep

import integration.TestLibrary
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * When a step generator proposes its step at all (`test-lib-std/src/TestChains.ard`): the
 * preconditions read off arend-lib's use of each construct.
 */
class ActivationTest {
  private object TestChains : TestModule("TestChains", TestLibrary::loadStd)

  /** Only the unfold heuristic; the meta is resolved the way the search resolves it. */
  private fun unfoldSteps(name: String): List<String> = TestChains.withGoal(name) { goal ->
    val module = TestChains.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = emptyList(), heuristics = setOf(Heuristic.UNFOLD),
    ).generate(goal, null).map { it.proof.toString() }
  }

  @Test
  fun `unfold is proposed only when it exposes a function or a case the goal lacks`() {
    assertEquals(listOf("unfold abs {?}"), unfoldSteps("unfold-needed"))
    val notNeeded = unfoldSteps("unfold-not-needed")
    assertTrue(notNeeded.isEmpty(), notNeeded.toString())
  }

  @Test
  fun `a hypothesis is applied only when it concludes what the goal is about`() {
    val module = TestChains.module
    val proposed = TestChains.withGoal("hyp-heads") { HypothesisGenerator(module.location).generate(it, null).map { step -> step.proof.toString() } }
    assertEquals(listOf("f {?}"), proposed)
  }

  @Test
  fun `a path is chained with only where its ends meet the goal's`() {
    val module = TestChains.module
    val proposed = TestChains.withGoal("path-ends") { PathGenerator(module.location, TestChains.scopeRef("*>"), TestChains.scopeRef("inv")).generate(it, null).map { step -> step.proof.toString() } }
    assertEquals(listOf("p *> {?}"), proposed)
  }
}
