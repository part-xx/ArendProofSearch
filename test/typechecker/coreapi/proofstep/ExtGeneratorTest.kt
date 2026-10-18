package typechecker.coreapi.proofstep

import integration.TestLibrary
import typechecker.coreapi.ArendGoal
import kotlin.test.Test

/** `ext` on equalities of propositions (`test-lib-std/src/TestRewrite.ard`). */
class ExtGeneratorTest {
  private object TestRewrite : TestModule("TestRewrite", TestLibrary::loadStd)

  private fun generator(): (ArendGoal) -> HeuristicStepGenerator = {
    val module = TestRewrite.module
    HeuristicStepGenerator(
      module.server.getCheckerFor(listOf(module.location)), module.server, module.libraryName, module.location.modulePath,
      retrievers = emptyList(),
    )
  }

  @Test
  fun `an equality of propositions is proved by ext from their equivalence`() {
    TestRewrite.assertProves(TestRewrite.search("iff-eq", generator()), "ext p")
  }
}
