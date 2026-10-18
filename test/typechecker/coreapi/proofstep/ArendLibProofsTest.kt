package typechecker.coreapi.proofstep

import integration.TestLibrary
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * The search proves the [ArendLibLemmas] again.
 *
 * Each search is given the global names its original proof uses: the premises to apply and the
 * decision functions to split on, standing in for premise selection; [ArendLibRetrievalTest]
 * retrieves them instead. The search expands one goal at a time and prefers states with
 * fewer open goals; without that, branches multiply each other's alternatives.
 */
class ArendLibProofsTest {
  private val modules = HashMap<String, TestModule>()

  private fun module(name: String) = modules.getOrPut(name) { TestModule(name, TestLibrary::loadStd) }

  @TestFactory
  fun `search proves arend-lib lemmas again`(): List<DynamicTest> = ArendLibLemmas.all.map { lemma ->
    DynamicTest.dynamicTest("${lemma.name} (${lemma.source})") {
      val module = module(lemma.module)
      val result = module.search(lemma.name, {
        val location = module.module.location
        HeuristicStepGenerator(
          module.module.server.getCheckerFor(listOf(location)), module.module.server, module.module.libraryName, location.modulePath,
          retrievers = listOf(FixedPremiseRetriever(lemma.premises)),
          splitters = lemma.splitters.map { PremiseCandidate(it) },
        )
      }, maxExpansions = 300, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
      println("PROOF ${lemma.name}: ${module.assertProves(result).replace("\n", " ")}")
    }
  }
}
