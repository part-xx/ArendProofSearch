package typechecker

import java.io.BufferedReader
import java.net.HttpURLConnection
import java.net.InetSocketAddress
import java.net.ServerSocket
import java.net.URI
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.ArrayDeque
import java.util.concurrent.TimeUnit

/**
 * A managed llama.cpp server backed by a local GGUF model.
 *
 * [start] loads the model, waits for llama-server's health endpoint, and returns
 * an ordinary [LLMClient]. Closing it stops the child server as well.
 */
class LocalLlamaLLMClient private constructor(
    private val process: Process,
    private val delegate: OpenAILikeLLMClient,
    val baseUrl: String,
    val modelPath: Path
) : LLMClient, AutoCloseable {

    private val shutdownHook = Thread({ terminate(process) }, "local-llama-shutdown")
    @Volatile
    private var closed = false

    init {
        Runtime.getRuntime().addShutdownHook(shutdownHook)
    }

    override suspend fun generateResponse(systemPrompt: String, userPrompt: String, temperature: Double?): String =
        delegate.generateResponse(systemPrompt, userPrompt, temperature)

    override suspend fun generateResponses(
        systemPrompt: String,
        userPrompt: String,
        temperature: Double?,
        count: Int
    ): List<String> = delegate.generateResponses(systemPrompt, userPrompt, temperature, count)

    override fun close() {
        if (closed) return
        closed = true
        delegate.close()
        terminate(process)
        try {
            Runtime.getRuntime().removeShutdownHook(shutdownHook)
        } catch (_: IllegalStateException) {
            // The JVM is already shutting down and is running the hook itself.
        }
    }

    companion object {
        /** Exact pre-Arend-fine-tuning parent recorded in the direct-v1 adapter metadata. */
        const val BASE_MODEL_ID = "Qwen/Qwen3-Coder-30B-A3B-Instruct"
        const val DEFAULT_MODEL_FILENAME =
            "qwen3-coder-30b-a3b-arend-direct-v1-production-20260823-001-q5_k_m.gguf"
        /** Context tokens available to each server slot. */
        const val DEFAULT_CONTEXT_SIZE = 8192
        const val DEFAULT_MAX_TOKENS = 512
        const val DEFAULT_PARALLEL = 1
        const val DEFAULT_STARTUP_TIMEOUT_SECONDS = 180L

        fun defaultModelPath(): Path =
            Paths.get("../VM_setup/models/$DEFAULT_MODEL_FILENAME").toAbsolutePath().normalize()

        fun start(
            modelPath: Path = defaultModelPath(),
            contextSize: Int = DEFAULT_CONTEXT_SIZE,
            maxTokens: Int = DEFAULT_MAX_TOKENS,
            parallel: Int = DEFAULT_PARALLEL,
            startupTimeoutSeconds: Long = DEFAULT_STARTUP_TIMEOUT_SECONDS,
            executable: String = System.getenv("LLAMA_SERVER") ?: "llama-server"
        ): LocalLlamaLLMClient {
            val resolvedModel = modelPath.toAbsolutePath().normalize()
            require(contextSize > 0) { "Local model context size must be positive" }
            require(maxTokens > 0) { "Local model max tokens must be positive" }
            require(parallel > 0) { "Local model parallelism must be positive" }
            require(contextSize <= Int.MAX_VALUE / parallel) {
                "Local model total context size is too large: $contextSize * $parallel"
            }
            require(startupTimeoutSeconds > 0) { "Local model startup timeout must be positive" }
            require(Files.isRegularFile(resolvedModel)) {
                "Local GGUF model not found: $resolvedModel"
            }

            val port = findFreePort()
            val baseUrl = "http://127.0.0.1:$port"
            val command = serverCommand(executable, resolvedModel, port, contextSize, parallel)
            val process = try {
                ProcessBuilder(command)
                    .redirectErrorStream(true)
                    .start()
            } catch (e: Exception) {
                throw IllegalStateException(
                    "Could not start '$executable'. Install llama.cpp (brew install llama.cpp) " +
                            "or set LLAMA_SERVER to the executable path.",
                    e
                )
            }
            val output = ProcessOutput(process.inputReader())

            try {
                waitUntilReady(baseUrl, process, output, startupTimeoutSeconds)
            } catch (e: Exception) {
                terminate(process)
                val details = output.tail().takeIf { it.isNotBlank() }?.let { "\nllama-server output:\n$it" } ?: ""
                throw IllegalStateException("Failed to load local model $resolvedModel: ${e.message}$details", e)
            }

            val delegate = OpenAILikeLLMClient(
                apiKey = "local",
                model = "",
                baseUrl = "$baseUrl/v1",
                maxTokens = maxTokens,
                // true means the provider-specific enable_thinking=false field is
                // omitted; llama-server follows the chat template stored in the GGUF.
                enableThinking = true
            )
            return LocalLlamaLLMClient(process, delegate, baseUrl, resolvedModel)
        }

        internal fun serverCommand(
            executable: String,
            modelPath: Path,
            port: Int,
            contextSize: Int,
            parallel: Int = DEFAULT_PARALLEL
        ): List<String> =
            listOf(
                executable,
                "--model", modelPath.toString(),
                "--host", "127.0.0.1",
                "--port", port.toString(),
                // llama.cpp divides the total context across parallel slots.
                "--ctx-size", (contextSize * parallel).toString(),
                "--gpu-layers", "all",
                "--parallel", parallel.toString(),
                // Match the production model's validated local launch profile.
                "--flash-attn", "on",
                "--cache-type-k", "q8_0",
                "--cache-type-v", "q8_0",
                "--temp", "0.7",
                "--top-k", "20",
                "--top-p", "0.8",
                "--min-p", "0",
                "--jinja",
                // Qwen3-Coder-Instruct supports only non-thinking output. This is
                // also harmless for templates with no reasoning branch.
                "--reasoning", "off",
                "--log-disable"
            )

        private fun findFreePort(): Int = ServerSocket().use { socket ->
            socket.reuseAddress = true
            socket.bind(InetSocketAddress("127.0.0.1", 0))
            socket.localPort
        }

        private fun waitUntilReady(
            baseUrl: String,
            process: Process,
            output: ProcessOutput,
            timeoutSeconds: Long
        ) {
            val deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSeconds)
            while (System.nanoTime() < deadline) {
                if (!process.isAlive) {
                    throw IllegalStateException(
                        "llama-server exited during startup with code ${process.exitValue()}" +
                                output.tail().takeIf { it.isNotBlank() }?.let { ": $it" }.orEmpty()
                    )
                }
                if (isHealthy("$baseUrl/health")) return
                Thread.sleep(500)
            }
            throw IllegalStateException("llama-server was not ready after $timeoutSeconds seconds")
        }

        private fun isHealthy(url: String): Boolean {
            val connection = URI(url).toURL().openConnection() as HttpURLConnection
            return try {
                connection.connectTimeout = 1_000
                connection.readTimeout = 1_000
                connection.requestMethod = "GET"
                connection.responseCode in 200..299
            } catch (_: Exception) {
                false
            } finally {
                connection.disconnect()
            }
        }

        private fun terminate(process: Process) {
            if (!process.isAlive) return
            process.destroy()
            try {
                if (!process.waitFor(10, TimeUnit.SECONDS)) {
                    process.destroyForcibly()
                    process.waitFor(10, TimeUnit.SECONDS)
                }
            } catch (_: InterruptedException) {
                process.destroyForcibly()
                Thread.currentThread().interrupt()
            }
        }
    }

    /** Drains subprocess output so a full pipe can never stall llama-server. */
    private class ProcessOutput(reader: BufferedReader) {
        private val lines = ArrayDeque<String>()

        init {
            Thread({
                reader.useLines { sequence ->
                    sequence.forEach { line ->
                        synchronized(lines) {
                            if (lines.size == 30) lines.removeFirst()
                            lines.addLast(line)
                        }
                    }
                }
            }, "local-llama-output").apply {
                isDaemon = true
                start()
            }
        }

        fun tail(): String = synchronized(lines) { lines.joinToString("\n") }
    }
}
