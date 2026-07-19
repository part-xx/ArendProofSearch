package typechecker

import io.ktor.client.*
import io.ktor.client.call.*
import io.ktor.client.plugins.*
import io.ktor.client.request.*
import io.ktor.client.statement.*
import io.ktor.http.*
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.withContext
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.*

/**
 * LLM Client implementation for OpenAI-compatible APIs.
 * 
 * This client works with any OpenAI-compatible API, including:
 * - OpenAI GPT models
 * - DeepSeek
 * - Alibaba Cloud Qwen/DeepSeek
 * - Groq
 * - Together AI
 * - Any self-hosted OpenAI-compatible server
 * 
 * API specification: https://platform.openai.com/docs/api-reference/chat
 */
class OpenAILikeLLMClient(
    private val apiKey: String,
    private val model: String = "qwen-math-plus",
    private val baseUrl: String = "https://ws-pzity02qkb8f5fja.ap-southeast-1.maas.aliyuncs.com/compatible-mode/v1"
) : LLMClient {

    private val httpClient = HttpClient {
        install(HttpTimeout) {
            requestTimeoutMillis = 30000  // 30 seconds
            connectTimeoutMillis = 10000  // 10 seconds
            socketTimeoutMillis = 30000   // 30 seconds
        }
    }

    /**
     * Generates a response from the OpenAI-compatible API.
     *
     * @param systemPrompt The system prompt to set the assistant's behavior
     * @param userPrompt The user's prompt/input
     * @return The generated response text
     */
    override suspend fun generateResponse(systemPrompt: String, userPrompt: String): String {
        return withContext(Dispatchers.Default) {
            try {
                val requestBody = """
                    {
                        "model": ${Json.encodeToString(model)},
                        "messages": [
                            {"role": "system", "content": ${Json.encodeToString(systemPrompt)}},
                            {"role": "user", "content": ${Json.encodeToString(userPrompt)}}
                        ]
                    }
                """

                val response: HttpResponse = httpClient.post("$baseUrl/chat/completions") {
                    header(HttpHeaders.Authorization, "Bearer $apiKey")
                    header(HttpHeaders.ContentType, "application/json")
                    setBody(requestBody)
                }

                val responseBody = response.body<String>()
                val json = Json.parseToJsonElement(responseBody)

                val choices = (json as JsonObject)["choices"]?.jsonArray
                val firstChoice = choices?.firstOrNull()
                val message = (firstChoice as? JsonObject)?.get("message")?.jsonObject
                val content = message?.get("content")?.jsonPrimitive?.content

                content ?: run {
                    throw RuntimeException("Failed to parse response: $responseBody")
                }

            } catch (e: Exception) {
                throw RuntimeException("Error calling API: ${e.message}", e)
            }
        }
    }

    /**
     * Creates an OpenAILikeLLMClient instance using environment variables or default values.
     *
     * Environment variables:
     * - OPENAI_LIKE_API_KEY: API key for any OpenAI-compatible API
     * - OPENAI_LIKE_MODEL: Model to use (default: gpt-4o)
     * - OPENAI_LIKE_BASE_URL: Base URL for the API endpoint (default: OpenAI)
     *
     * For DeepSeek or other OpenAI-compatible services:
     * - Set OPENAI_LIKE_BASE_URL to the service's endpoint
     * - Set OPENAI_LIKE_MODEL to the desired model name
     */
    companion object {
        fun createFromEnvironment(): OpenAILikeLLMClient {
            val apiKey = System.getenv("OPENAI_LIKE_API_KEY")
                ?: System.getProperty("openai.like.api.key")
                ?: error("API key not provided. Set OPENAI_LIKE_API_KEY environment variable or openai.like.api.key system property.")

            val model = System.getenv("OPENAI_LIKE_MODEL")
                ?: System.getProperty("openai.like.model")
                ?: "qwen-math-plus"

            val baseUrl = System.getenv("OPENAI_LIKE_BASE_URL")
                ?: System.getProperty("openai.like.base.url")
                ?: "https://ws-pzity02qkb8f5fja.ap-southeast-1.maas.aliyuncs.com/compatible-mode/v1"

            return OpenAILikeLLMClient(apiKey, model, baseUrl)
        }
    }
}
