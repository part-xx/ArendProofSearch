package typechecker

/**
 * Simple LLM client interface for proof search.
 * Implement this interface to use different LLM backends.
 */
interface LLMClient {
    suspend fun generateResponse(systemPrompt: String, userPrompt: String): String
}

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
    override suspend fun generateResponse(systemPrompt: String, userPrompt: String): String {
        return "Fallback: LLM not configured"
    }
}
