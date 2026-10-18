package typechecker

import kotlinx.serialization.json.jsonObject
import kotlinx.serialization.json.jsonPrimitive
import kotlin.test.Test
import kotlin.test.assertEquals

class OpenAILikeLLMClientTest {
    @Test
    fun `blank system prompt is sent explicitly to suppress template defaults`() {
        val messages = OpenAILikeLLMClient.chatMessages("", "compact Arend prompt")

        assertEquals(2, messages.size)
        assertEquals("system", messages[0].jsonObject["role"]?.jsonPrimitive?.content)
        assertEquals("", messages[0].jsonObject["content"]?.jsonPrimitive?.content)
        assertEquals("user", messages[1].jsonObject["role"]?.jsonPrimitive?.content)
        assertEquals("compact Arend prompt", messages[1].jsonObject["content"]?.jsonPrimitive?.content)
    }
}
