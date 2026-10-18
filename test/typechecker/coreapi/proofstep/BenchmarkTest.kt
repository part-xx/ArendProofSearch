package typechecker.coreapi.proofstep

import integration.TestLibrary
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Test
import search.best_first.BestFirstSearch
import typechecker.Proof
import typechecker.cli.CliConnection
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardOpenOption

/**
 * The proof-search benchmark: every lemma of `bench-lib` (arend-lib lemmas restated with `{?}`
 * bodies by `gen_bench.py`) is searched with retrieved premises, the original excluded, under a
 * fixed budget. Outcomes go to `$TMPDIR/arend-bench.log`, a summary per module to stdout.
 *
 * Opt-in: `-Dbench=true`; `-Dbench.modules=Bench_Arith_Nat,...` selects modules, `-Dbench.names=a,b`
 * lemmas by name, `-Dbench.limit=N` the number of lemmas, `-Dbench.log=path` the log file,
 * `-Dbench.expansions=N` the expansion budget per lemma (3000; the 10 s clock is the real limit), `-Dbench.seconds=N` the clock limit per lemma (10 s). Needs the daemon for test-lib-std (the `-ps` queries) and runs for hours.
 */
class BenchmarkTest {
  @Serializable
  class Lemma(val name: String, val module: String, val source: String, val inClass: String? = null)

  private val benchDir: Path = Paths.get(System.getProperty("user.dir"), "bench-lib")

  @Test
  fun benchmark() {
    assumeTrue(System.getProperty("bench") == "true", "Benchmark is opt-in: -Dbench=true")
    val cli = CliConnection(TestLibrary.testLibStdDir)
    val library = TestLibrary.load(benchDir, listOfNotNull(TestLibrary.arendLibsDir)) ?: error("bench-lib did not load")
    val all = Json { ignoreUnknownKeys = true }.decodeFromString<List<Lemma>>(Files.readString(benchDir.resolve("bench.json")))
    val modules = System.getProperty("bench.modules")?.split(',')?.toSet()
    val names = System.getProperty("bench.names")?.split(',')?.toSet()
    val limit = System.getProperty("bench.limit")?.toIntOrNull() ?: Int.MAX_VALUE
    val expansions = System.getProperty("bench.expansions")?.toIntOrNull() ?: 3000
    val seconds = System.getProperty("bench.seconds")?.toLongOrNull() ?: 10L
    val lemmas = all.filter { (modules == null || it.module in modules) && (names == null || it.name in names) }.take(limit)
    val log = System.getProperty("bench.log")?.let { Paths.get(it) } ?: Paths.get(System.getProperty("java.io.tmpdir"), "arend-bench.log")
    val index = SignatureIndex(cli)
    val premiseRetriever = ProofSearchRetriever(index)
    val equationRetriever = EquationRetriever(index)
    val splitRetriever = SplitRetriever(index)
    val destructorRetriever = DestructorRetriever(index)
    val benchModules = all.map { it.module }.toSet()
    val results = LinkedHashMap<String, MutableList<Boolean>>()

    // Indexing the library is a preprocessing step shared by every lemma: one proof search per symbol
    // that any statement of the benchmark is about (its head, the heads of its hypotheses), and `=`.
    // It is done before the searches, whose clock is the budget per lemma.
    val indexingStart = System.currentTimeMillis()
    // The heads that subgoals of most statements have, besides the statements' own: equations, orders, disjunctions, refutations
    val symbols = LinkedHashSet<String>().apply { addAll(listOf("=", "<=", "<", "Not", "Empty")) }
    val warmUps = ArrayList<() -> Unit>()
    for (lemma in lemmas) {
      try {
        val module = TestModule(lemma.module, { library })
        module.withGoal(lemma.name) { goal ->
          PremiseRetriever.head(goal.expectedType)?.let { symbols.add(it.name) }
          goal.typechecker.context.values.forEach { binding -> PremiseRetriever.head(binding.type)?.let { symbols.add(it.name) } }
          // The functions of the statement and of its hypotheses: their lemmas are split on, and a variable-headed goal is searched by them
          splitRetriever.symbols(goal).forEach { symbols.add(it.name) }
          destructorRetriever.symbols(goal).forEach { symbols.add(it.name) }
          goal.typechecker.context.values.forEach { binding -> EquationRetriever.functionSymbols(binding.type).take(2).forEach { symbols.add(it.name) } }
          // Resolving the retrieved names to definitions is library-wide work too
          val location = module.module.location
          val generator = HeuristicStepGenerator(
            module.module.server.getCheckerFor(listOf(location)), module.module.server, module.module.libraryName, location.modulePath,
            retrievers = listOf(ConstructorRetriever(), premiseRetriever), rewriteRetrievers = listOf(equationRetriever),
            splitRetrievers = listOf(splitRetriever), destructorRetrievers = listOf(destructorRetriever),
            transferRetrieverFactory = { conversions -> TransferRetriever(index, conversions) },
          )
          // The twin symbols of the statement under the structure conversions (`negative` for `inverse`)
          symbols.addAll(generator.transferSymbols(goal))
          warmUps.add { generator.warmUp(goal) }
        }
      } catch (e: Throwable) {
        // A statement that does not typecheck is reported when it is searched
      }
    }
    symbols.forEach { index.bySymbol(it) }
    warmUps.forEach { it() }
    println("Indexed ${symbols.size} symbols in ${System.currentTimeMillis() - indexingStart} ms")
    // A symbol first met inside a search (a subgoal's new head) is indexed in the background, not on the lemma's clock
    index.deferUnindexed = true

    for (lemma in lemmas) {
      val module = TestModule(lemma.module, { library })
      val excluded: (PremiseCandidate) -> Boolean = { candidate ->
        candidate.module in benchModules ||
          (candidate.module == lemma.source && (candidate.name == lemma.name || candidate.name.endsWith(".${lemma.name}")))
      }
      fun excluding(retriever: PremiseRetriever) = object : PremiseRetriever {
        override fun retrieve(goal: ArendGoal) = retriever.retrieve(goal).filterNot(excluded)
      }
      var start = System.currentTimeMillis()
      val outcome = try {
        module.withGoal(lemma.name) { goal ->
          start = System.currentTimeMillis()
          val location = module.module.location
          val generator = HeuristicStepGenerator(
            module.module.server.getCheckerFor(listOf(location)), module.module.server, module.module.libraryName, location.modulePath,
            retrievers = listOf(excluding(ConstructorRetriever()), excluding(premiseRetriever)),
            rewriteRetrievers = listOf(EquationRetriever(index, excluded = excluded)),
            splitRetrievers = listOf(excluding(splitRetriever)),
            destructorRetrievers = listOf(excluding(destructorRetriever)),
            transferRetrieverFactory = { conversions -> TransferRetriever(index, conversions) },
            splitters = HeuristicStepGenerator.DEFAULT_SPLITTERS.filterNot(excluded),
          )
          val initialProof = object : Proof<ArendGoal> {
            override fun goals() = listOf(goal)
            override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = proof
          }
          val proof = BestFirstSearch(generator, maxExpansions = expansions, focusFirstGoal = true, openGoalCost = 1.0, maxDepth = 20, maxMillis = seconds * 1000).search(initialProof) as? ArendProof
          if (proof != null && proof.isFinished()) {
            val (source, imports) = proof.qualifiedSource(generator.moduleScope())
            "PROVED ${lemma.name} ${source.replace("\n", " ")} -- imports: ${imports.joinToString(", ")}"
          } else "UNPROVED ${lemma.name}"
        }
      } catch (e: Throwable) {
        "ERROR ${lemma.name} ${e.javaClass.simpleName}: ${e.message?.lineSequence()?.firstOrNull()} at ${(e.stackTrace.take(2) + e.stackTrace.filter { it.className.startsWith("typechecker") || it.className.startsWith("search") }.take(6)).joinToString(" < ")}"
      }
      val line = "${lemma.module} $outcome (${System.currentTimeMillis() - start}ms)"
      println(line)
      Runtime.getRuntime().let { println("Heap used ${(it.totalMemory() - it.freeMemory()) / 1_000_000} MB of ${it.maxMemory() / 1_000_000} MB") }
      Files.writeString(log, line + "\n", StandardOpenOption.CREATE, StandardOpenOption.APPEND)
      results.getOrPut(lemma.module) { mutableListOf() }.add(outcome.startsWith("PROVED"))
    }
    for ((module, outcomes) in results) {
      println("SUMMARY $module: ${outcomes.count { it }} / ${outcomes.size} proved")
    }
    val total = results.values.flatten()
    println("SUMMARY TOTAL: ${total.count { it }} / ${total.size} proved (${if (total.isEmpty()) 0 else 100 * total.count { it } / total.size}%)")
  }
}
