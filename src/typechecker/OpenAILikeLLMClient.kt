package typechecker

import io.ktor.client.*
import io.ktor.client.call.*
import io.ktor.client.plugins.*
import io.ktor.client.request.*
import io.ktor.client.statement.*
import io.ktor.http.*
import kotlinx.coroutines.*
import kotlinx.coroutines.time.*
import kotlinx.serialization.json.*
import kotlin.time.Duration.Companion.milliseconds

class OpenAILikeLLMClient(
    private val apiKey: String,
    private val model: String = "qwen-math-plus",
    private val baseUrl: String = "https://ws-pzity02qkb8f5fja.ap-southeast-1.maas.aliyuncs.com/compatible-mode/v1",
    private val maxTokens: Int = 1024,
    private val enableThinking: Boolean = false
) : LLMClient {

    private val httpClient = HttpClient {
        install(HttpTimeout) {
            requestTimeoutMillis = 120000
            connectTimeoutMillis = 15000
            socketTimeoutMillis = 120000
        }
    }

    override suspend fun generateResponse(systemPrompt: String, userPrompt: String, temperature: Double?): String {
        var lastException: Exception? = null

        for (attempt in 1..3) {
            val response = try {
                withTimeout(120000.milliseconds) {
                    val requestBody = buildJsonObject {
                        put("model", model)
                        putJsonArray("messages") {
                            add(buildJsonObject {
                                put("role", "system")
                                put("content", systemPrompt)
                            })
                            add(buildJsonObject {
                                put("role", "user")
                                put("content", userPrompt)
                            })
                        }
                        put("max_tokens", maxTokens)
                        if (temperature != null) put("temperature", temperature)
                        // DashScope/Alibaba compatible-mode extra param: disables long
                        // chain-of-thought on hybrid (Qwen3-style) models. Ignored elsewhere.
                        if (!enableThinking) {
                            put("enable_thinking", false)
                        }
                    }.toString()

                    httpClient.post("$baseUrl/chat/completions") {
                        header(HttpHeaders.Authorization, "Bearer $apiKey")
                        header(HttpHeaders.ContentType, "application/json")
                        setBody(requestBody)
                    }
                }
            } catch (e: Exception) {
                lastException = e
                if (attempt < 3) {
                    val delayMs = 2000L * attempt * attempt
                    println("API attempt $attempt failed: ${e.message}. Retrying in ${delayMs}ms...")
                    delay(delayMs.milliseconds)
                }
                null
            }

            if (response != null) {
                val responseBody = response.body<String>()
                val json = Json.parseToJsonElement(responseBody)
                val choices = (json as JsonObject)["choices"]?.jsonArray
                val firstChoice = choices?.firstOrNull()
                val message = (firstChoice as? JsonObject)?.get("message")?.jsonObject
                val content = message?.get("content")?.jsonPrimitive?.content

                content?.let { return stripThinking(it) }

                throw RuntimeException("Failed to parse response: $responseBody")
            }
        }

        throw RuntimeException("Error calling API after 3 attempts: ${lastException?.message}", lastException)
    }

    /**
     * Removes chain-of-thought blocks that some models emit inline in the content
     * (<think>...</think>), including an unclosed trailing block cut off by max_tokens.
     */
    private fun stripThinking(content: String): String {
        var result = content.replace(Regex("<think>.*?</think>", RegexOption.DOT_MATCHES_ALL), "")
        result = result.replace(Regex("<think>.*$", RegexOption.DOT_MATCHES_ALL), "")
        return result.trim()
    }

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

            val maxTokens = (System.getenv("OPENAI_LIKE_MAX_TOKENS")
                ?: System.getProperty("openai.like.max.tokens"))?.toIntOrNull() ?: 1024

            val enableThinking = (System.getenv("OPENAI_LIKE_ENABLE_THINKING")
                ?: System.getProperty("openai.like.enable.thinking"))?.toBoolean() ?: false

            return OpenAILikeLLMClient(apiKey, model, baseUrl, maxTokens, enableThinking)
        }
    }
}
