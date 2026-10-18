package typechecker.coreapi.proofstep

import integration.TestLibrary
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import typechecker.cli.CliConnection
import typechecker.coreapi.ArendGoal
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardOpenOption
import kotlin.test.fail

/**
 * The search proves the [ArendLibLemmas] again with premises it retrieves itself: constructors
 * by [ConstructorRetriever], lemmas to apply by [ProofSearchRetriever], equations to rewrite with
 * by [EquationRetriever], and the default splitters. The original of each lemma is excluded from everything retrieved.
 *
 * Retrieval queries the Arend CLI's proof search through a daemon, which has to be running:
 * `java -jar cli-full.jar -L ../arend-lang-new/Arend test-lib-std -d`; without one the tests are skipped.
 * A query still takes seconds, so the retrievers are shared and cache their results.
 */
class ArendLibRetrievalTest {
  companion object {
    private val cli: CliConnection? by lazy {
      try {
        CliConnection(TestLibrary.testLibStdDir)
      } catch (e: Exception) {
        println("No Arend daemon for test-lib-std: ${e.message}")
        null
      }
    }
    /** Each lemma's outcome is also appended here: a run takes half an hour, and Gradle keeps results only at its end. */
    private val outcomeLog: Path = Paths.get(System.getProperty("java.io.tmpdir"), "arend-lib-retrieval.log")

    private fun logOutcome(line: String) {
      println(line)
      Files.writeString(outcomeLog, line + "\n", StandardOpenOption.CREATE, StandardOpenOption.APPEND)
    }

    private val index by lazy { SignatureIndex(cli!!) }
    private val premiseRetriever by lazy { ProofSearchRetriever(index) }
    private val equationRetriever by lazy { EquationRetriever(index) }

    /**
     * Lemmas the search does not prove with retrieved premises, and why. In every case retrieval
     * never supplies a premise of the original proof, at any goal the search visits (measured).
     */
    val KNOWN_FAILURES: Map<String, String> = run {
      mapOf(
        "TotalOrder-meet-isMin'" to "not proved within the budget with retrieved premises",
        "CMonoid-pow_*-comm'" to "pow-comm, then *-comm: not proved within the budget with retrieved premises",
      )
    }
  }

  /** [retriever] without the candidates [excluded] rejects. */
  private class Excluding(private val retriever: PremiseRetriever, private val excluded: (PremiseCandidate) -> Boolean) : PremiseRetriever {
    override fun retrieve(goal: ArendGoal): List<PremiseCandidate> = retriever.retrieve(goal).filterNot(excluded)
  }

  private val modules = HashMap<String, TestModule>()

  private fun module(name: String) = modules.getOrPut(name) { TestModule(name, TestLibrary::loadStd) }

  /** Candidates the search must not use for [lemma]: its original, and the restated lemmas, which all still have goals. */
  private fun excluded(lemma: ArendLibLemmas.Lemma): (PremiseCandidate) -> Boolean =
    { lemma.isOriginal(it) || ArendLibLemmas.all.any { other -> other.module == it.module } }

  @TestFactory
  fun `search proves arend-lib lemmas again with retrieved premises`(): List<DynamicTest> = ArendLibLemmas.all.map { lemma ->
    DynamicTest.dynamicTest("${lemma.name} (${lemma.source})") {
      assumeTrue(cli != null, "No Arend daemon for test-lib-std")
      val excluded = excluded(lemma)
      val module = module(lemma.module)
      val start = System.currentTimeMillis()
      val result = module.search(lemma.name, {
        val location = module.module.location
        HeuristicStepGenerator(
          module.module.server.getCheckerFor(listOf(location)), module.module.server, module.module.libraryName, location.modulePath,
          retrievers = listOf(Excluding(ConstructorRetriever(), excluded), Excluding(premiseRetriever, excluded)),
          rewriteRetrievers = listOf(Excluding(equationRetriever, excluded)),
          splitters = HeuristicStepGenerator.DEFAULT_SPLITTERS.filterNot(excluded),
        )
      }, maxExpansions = 300, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20)
      val time = System.currentTimeMillis() - start
      val knownFailure = KNOWN_FAILURES[lemma.name]
      if (knownFailure != null) {
        result.proof?.let {
          logOutcome("PROVED-NOW ${lemma.name} in ${time}ms: ${it.toString().replace("\n", " ")}")
          fail("${lemma.name} is proved now; remove it from KNOWN_FAILURES")
        }
        logOutcome("UNPROVED ${lemma.name} in ${time}ms: $knownFailure")
      } else {
        if (result.proof == null) logOutcome("FAILED ${lemma.name} in ${time}ms")
        logOutcome("PROOF ${lemma.name} in ${time}ms: ${module.assertProves(result).replace("\n", " ")}")
      }
    }
  }
}
