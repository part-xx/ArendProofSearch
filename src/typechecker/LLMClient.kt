package typechecker

/**
 * Simple LLM client interface for proof search.
 * Implement this interface to use different LLM backends.
 */
interface LLMClient {
    suspend fun generateResponse(systemPrompt: String, userPrompt: String, temperature: Double? = null): String
}

/**
 * Thrown when the LLM backend is unreachable or keeps failing after client-side
 * retries (network, VPN, endpoint, auth). Distinct from proof-search failures:
 * aborts the search rather than being treated as "no proof found".
 */
class LLMUnavailableException(message: String, cause: Throwable? = null) : RuntimeException(message, cause)

/**
 * Example LLM client implementation (commented out - use JetBrains/koog or other backend later)
 */
//class JetBrainsLLMClient(
//    private val executor: PromptExecutor,
//    private val model: LLModel
//) : LLMClient {
//    override suspend fun generateResponse(systemPrompt: String, userPrompt: String): String {
//        val agent = AIAgent(
//            executor = executor,
//            systemPrompt = systemPrompt,
//            llmModel = model
//        )
//        return agent.run(userPrompt)
//    }
//}

/**
 * Fallback LLM client that returns empty responses (for building without LLM dependencies)
 */
class FallbackLLMClient : LLMClient {
    override suspend fun generateResponse(systemPrompt: String, userPrompt: String, temperature: Double?): String {
        return "Fallback: LLM not configured"
    }
}
