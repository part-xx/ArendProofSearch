package typechecker

import java.nio.file.Paths
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class LocalLlamaLLMClientTest {
    @Test
    fun `default model is the neighboring Qwen3 direct-v1 GGUF`() {
        val path = LocalLlamaLLMClient.defaultModelPath()
        assertEquals("Qwen/Qwen3-Coder-30B-A3B-Instruct", LocalLlamaLLMClient.BASE_MODEL_ID)
        assertEquals(
            "qwen3-coder-30b-a3b-arend-direct-v1-production-20260823-001-q5_k_m.gguf",
            LocalLlamaLLMClient.DEFAULT_MODEL_FILENAME
        )
        assertEquals(LocalLlamaLLMClient.DEFAULT_MODEL_FILENAME, path.fileName.toString())
        assertEquals(512, LocalLlamaLLMClient.DEFAULT_MAX_TOKENS)
        assertTrue(path.toString().contains("VM_setup"))
    }

    @Test
    fun `server command loads the model with the requested context`() {
        val command = LocalLlamaLLMClient.serverCommand(
            executable = "/opt/bin/llama-server",
            modelPath = Paths.get("/models/arend.gguf"),
            port = 8123,
            contextSize = 4096
        )

        assertEquals("/opt/bin/llama-server", command.first())
        assertEquals("/models/arend.gguf", command[command.indexOf("--model") + 1])
        assertEquals("8123", command[command.indexOf("--port") + 1])
        assertEquals("4096", command[command.indexOf("--ctx-size") + 1])
        assertTrue("--jinja" in command)
        assertEquals("off", command[command.indexOf("--reasoning") + 1])
        assertEquals("on", command[command.indexOf("--flash-attn") + 1])
        assertEquals("q8_0", command[command.indexOf("--cache-type-k") + 1])
        assertEquals("q8_0", command[command.indexOf("--cache-type-v") + 1])
        assertEquals("0.7", command[command.indexOf("--temp") + 1])
        assertEquals("20", command[command.indexOf("--top-k") + 1])
        assertEquals("0.8", command[command.indexOf("--top-p") + 1])
        assertEquals("0", command[command.indexOf("--min-p") + 1])
    }

    @Test
    fun `server command reserves a full context for every parallel completion`() {
        val command = LocalLlamaLLMClient.serverCommand(
            executable = "llama-server",
            modelPath = Paths.get("/models/base.gguf"),
            port = 8123,
            contextSize = 4096,
            parallel = 10
        )

        assertEquals("40960", command[command.indexOf("--ctx-size") + 1])
        assertEquals("10", command[command.indexOf("--parallel") + 1])
    }
}
