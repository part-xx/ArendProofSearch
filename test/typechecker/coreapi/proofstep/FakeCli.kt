package typechecker.coreapi.proofstep

import typechecker.cli.ApplyStepResponse
import typechecker.cli.CliApi
import typechecker.cli.FindGoalsResponse
import typechecker.cli.ProofSearchResponse
import typechecker.cli.ScopeResponse
import typechecker.cli.SearchResult
import typechecker.cli.SignatureInfoResponse
import typechecker.cli.TypeExprResponse

/** Answers proof searches from [results], keyed by pattern, and records the patterns asked for. */
class FakeCli(private val results: Map<String, List<SearchResult>>) : CliApi {
  val patterns = mutableListOf<String>()

  override fun proofSearch(pattern: String): ProofSearchResponse {
    patterns.add(pattern)
    val found = results[pattern].orEmpty()
    return ProofSearchResponse(found, found.size)
  }

  override fun findGoals(moduleDef: String): FindGoalsResponse = throw UnsupportedOperationException()
  override fun applyStep(moduleDef: String, fullBody: String): ApplyStepResponse = throw UnsupportedOperationException()
  override fun getScope(moduleDef: String, goalId: String): ScopeResponse = throw UnsupportedOperationException()
  override fun signature(moduleDef: String): String = throw UnsupportedOperationException()
  override fun signatureInfo(moduleDef: String, name: String): SignatureInfoResponse? = throw UnsupportedOperationException()
  override fun typeExpr(moduleDef: String, goalId: String, expression: String, proofBody: String?): TypeExprResponse? =
    throw UnsupportedOperationException()
}

fun searchResult(name: String, expression: String, module: String = "TestApp") =
  SearchResult(module = module, name = name, kind = "LEMMA", expression = expression)
