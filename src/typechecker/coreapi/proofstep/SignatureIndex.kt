package typechecker.coreapi.proofstep

import typechecker.cli.CliApi
import typechecker.cli.SearchResult

/**
 * The definitions mentioning a symbol, with their full signatures, from one proof search per
 * symbol (`-ps S print-full`, uncapped). Retrievers used to ask for each combination of symbols
 * and hypotheses separately (`<= \and meet`, `Nat -> <=`), several queries of a few seconds per
 * goal; what those add is read off the full signatures here instead, and the answer for a symbol
 * is kept for every goal that mentions it.
 */
class SignatureIndex(private val cli: CliApi) {
  /** A definition found: its [parameters] and the [codomain] of its result type, as printed, plus the whole [text]. */
  class Entry(val name: String, val module: String, val parameters: String, val codomain: List<String>, val text: String)

  private val cache = HashMap<String, List<Entry>>()
  private val pending = HashSet<String>()
  private val background by lazy { java.util.concurrent.Executors.newSingleThreadExecutor { r -> Thread(r, "signature-index").apply { isDaemon = true } } }

  /**
   * When set, a symbol not indexed yet gets no results now and is fetched in the background for
   * later goals: a search under a clock cannot wait seconds for the daemon. [BenchmarkTest] sets it
   * once the symbols of the statements are indexed.
   */
  @Volatile var deferUnindexed = false

  fun bySymbol(symbol: Symbol): List<Entry> = bySymbol(symbol.name)

  fun bySymbol(name: String): List<Entry> {
    synchronized(cache) { cache[name]?.let { return it } }
    if (deferUnindexed) {
      synchronized(cache) { if (pending.add(name)) background.submit { fetch(name) } }
      return emptyList()
    }
    return fetch(name)
  }

  /** Whether [name] has been indexed. */
  fun isIndexed(name: String): Boolean = synchronized(cache) { name in cache }

  private fun fetch(name: String): List<Entry> {
    val entries = try {
      val start = System.currentTimeMillis()
      val results = cli.proofSearch(name, 0, true).results
      val millis = System.currentTimeMillis() - start
      if (millis >= PremiseRetriever.SLOW_QUERY_MILLIS) println("Slow proof search (${millis}ms, ${results.size} results): $name")
      results.map(::entry)
    } catch (e: Exception) {
      println("Proof search failed for '$name': ${e.message}")
      emptyList()
    }
    synchronized(cache) { cache[name] = entries; pending.remove(name) }
    return entries
  }

  companion object {
    /**
     * Parses a result: the full signature `\lemma f {A : X} (p : P) : T \elim x` when printed, or
     * otherwise the matching slice `p1 -> ... -> codomain`.
     */
    fun entry(result: SearchResult): Entry {
      if (result.signature.isBlank()) {
        val tokens = ProofSearchRetriever.topLevelTokens(result.expression)
        val arrow = tokens.lastIndexOf("->")
        return Entry(result.name, result.module, tokens.subList(0, maxOf(arrow, 0)).joinToString(" "), tokens.subList(arrow + 1, tokens.size), result.expression)
      }
      if (result.kind == "CONSTRUCTOR") {
        // `| r-con P Q`: the parameter types; the codomain is the data type, which qualifies the name (`R.r-con`)
        val tokens = ProofSearchRetriever.topLevelTokens(result.signature).dropWhile { it == "|" }.drop(1)
        val data = result.name.substringBeforeLast('.', "")
        return Entry(result.name, result.module, tokens.joinToString(" "), listOf(data), "${result.signature} : $data")
      }
      // A field prints as `| <=-transitive {x y z : E} : x <= y -> y <= z -> x <= z`, like a lemma after the bar
      var tokens = ProofSearchRetriever.topLevelTokens(result.signature).dropWhile { it == "|" }
      // What follows the type is not part of it
      val elim = tokens.indexOf("\\elim")
      if (elim >= 0) tokens = tokens.subList(0, elim)
      val colon = tokens.indexOf(":")
      val parameters = if (colon < 0) emptyList() else tokens.subList(0, colon).filter { it.startsWith("(") || it.startsWith("{") }
      val type = if (colon < 0) tokens else tokens.subList(colon + 1, tokens.size)
      return Entry(result.name, result.module, parameters.joinToString(" "), ProofSearchRetriever.codomainTokens(type.joinToString(" ")), result.signature)
    }
  }
}
