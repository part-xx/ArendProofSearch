package org.jetbrains.ai.kotlin.playbook

import ai.dev.kit.clients.instrument
import com.openai.client.OpenAIClient
import com.openai.client.okhttp.OpenAIOkHttpClient
import com.openai.models.ChatModel
import com.openai.models.audio.speech.SpeechCreateParams
import com.openai.models.chat.completions.*
import com.openai.models.embeddings.EmbeddingCreateParams
import com.openai.models.embeddings.EmbeddingModel
import com.openai.models.images.ImageGenerateParams
import com.openai.models.images.ImageModel
import io.ktor.client.*
import io.ktor.client.engine.cio.*
import io.ktor.client.plugins.websocket.*
import io.ktor.client.request.*
import io.ktor.client.statement.*
import io.ktor.http.*
import io.ktor.websocket.*
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.jsonPrimitive
import java.io.File
import java.time.Duration
import java.util.*
import kotlin.jvm.optionals.getOrNull


private const val LITELLM_HOST = "litellm.labs.jb.gg"

private val gradleProps: java.util.Properties by lazy {
    java.util.Properties().apply {
        val f = java.io.File("gradle.properties")
        if (f.exists()) f.reader().use { load(it) }
    }
}

val LITELLM_URL: String = gradleProps.getProperty("llmBaseUrl")?.takeIf { it.isNotEmpty() }
    ?: System.getenv("LLM_BASE_URL")
    ?: "https://$LITELLM_HOST"
val LITELLM_API_KEY: String = gradleProps.getProperty("llmApiKey")?.takeIf { it.isNotEmpty() }
    ?: System.getenv("LLM_API_KEY")
    ?: System.getenv("LITELLM_API_KEY")
    ?: gradleProps.getProperty("litellmApiKey")?.takeIf { it.isNotEmpty() }
    ?: error("Set llmApiKey in gradle.properties (or LLM_API_KEY env var)")
val LLM_MODEL_ID: String = gradleProps.getProperty("llmModel")?.takeIf { it.isNotEmpty() }
    ?: System.getenv("LLM_MODEL")
    ?: "deepseek-chat"

fun createOpenAIClient(instrument: Boolean): OpenAIClient {
    return OpenAIOkHttpClient.builder()
        .baseUrl(LITELLM_URL)
        .apiKey(LITELLM_API_KEY)
        .timeout(Duration.ofSeconds(60))
        .build()
        .apply {
            if (instrument) {
                instrument(this)
            }
        }
}

inline fun <T> withOpenAI(instrument: Boolean = false, block: (OpenAIClient) -> T): T {
    return block(createOpenAIClient(instrument))
}

fun listModels(): List<String> = withOpenAI { client ->
    return client.models().list().data().map { it.id() }
}

fun createChatCompletion(model: ChatModel, userMessage: String, seed: Long? = null, instrument: Boolean = false): ChatCompletion =
    withOpenAI(instrument) { client ->
        val params = ChatCompletionCreateParams.builder()
            .addSystemMessage("You are a helpful assistant!")
            .addUserMessage(userMessage)
            .model(model)
            .seed(seed)
            .build()

        return client.chat().completions().create(params)
    }

fun getChatCompletionMessage(model: ChatModel, userMessage: String, instrument: Boolean = false): String? = withOpenAI { client ->
    val completion = createChatCompletion(model, userMessage, instrument = instrument)
    return completion.choices().first().message().content().getOrNull()
}

private fun loadImageAsBase64(resourcePath: String): String {
    val classLoader = Thread.currentThread().contextClassLoader
    val imageFile = classLoader.getResource(resourcePath)?.file?.let { File(it) }
        ?: error("Could not find image at $resourcePath")
    return Base64.getEncoder().encodeToString(imageFile.readBytes())
}

fun analyzeImage(imagePath: String, model: ChatModel, instrument: Boolean): String? = withOpenAI(instrument) { client ->
    val base64Image = loadImageAsBase64(imagePath)

    val contentParts = listOf<ChatCompletionContentPart>(
        ChatCompletionContentPart.ofImageUrl(
            ChatCompletionContentPartImage.builder()
                .imageUrl(
                    ChatCompletionContentPartImage.ImageUrl.builder()
                        .url("data:image/jpeg;base64,${base64Image}")
                        .build()
                )
                .build()
        ),
        ChatCompletionContentPart.ofText(
            ChatCompletionContentPartText.builder()
                .text("Please describe what you see in this image.")
                .build()
        )
    )

    val params = ChatCompletionCreateParams.builder()
        .model(model)
        .addUserMessageOfArrayOfContentParts(contentParts)
        .build()

    return client.chat().completions().create(params).choices().first().message().content().getOrNull()
}

suspend fun generateImage(prompt: String, instrument: Boolean = false): String = withOpenAI(instrument) { client ->
    val params = ImageGenerateParams.builder()
        .prompt(prompt)
        .model(ImageModel.DALL_E_2)
        .size(ImageGenerateParams.Size._256X256)
        .n(1)
        .build()

    val images = client.images().generate(params)
    val imageUrl = images.data().get().first().url().get()

    HttpClient().use { httpClient ->
        val imageBytes = httpClient.get(imageUrl).readRawBytes()
        return Base64.getEncoder().encodeToString(imageBytes)
    }
}

fun saveImage(base64Image: String, outputPath: String) {
    val imageBytes = Base64.getDecoder().decode(base64Image)
    File(outputPath).apply { parentFile?.mkdirs() }.writeBytes(imageBytes)
}

fun createEmbeddings(text: String, model: EmbeddingModel, instrument: Boolean = false): List<Float> =
    withOpenAI(instrument) { client ->
        client.embeddings().create(
            EmbeddingCreateParams.builder()
                .model(model)
                .input(text)
                .build()
        ).data().first().embedding()
    }

fun textToSpeech(
    input: String,
    modelId: String,
    filePath: String,
    voice: SpeechCreateParams.Voice = SpeechCreateParams.Voice.ALLOY,
    responseFormat: SpeechCreateParams.ResponseFormat = SpeechCreateParams.ResponseFormat.MP3,
    instrument: Boolean = false
): File = withOpenAI(instrument) { client ->
    val speech = client.audio().speech().create(
        SpeechCreateParams.builder()
            .input(input)
            .model(modelId)
            .voice(voice)
            .responseFormat(responseFormat)
            .build()
    )

    val file = File(filePath).apply { parentFile?.mkdirs() }
    file.writeBytes(speech.body().readAllBytes())

    return file
}

fun realtimeApi(modelId: String, message: String): JsonObject? {
    val client = HttpClient(CIO) {
        install(WebSockets)
    }

    var response: JsonObject? = null

    runBlocking {
        client.webSocket(
            host = LITELLM_HOST,
            path = "realtime",
            request = {
                url.parameters.append("model", modelId)
                header(HttpHeaders.Authorization, "Bearer $LITELLM_API_KEY")
                header("OpenAI-Beta", "realtime=v1")
            },
        ) {
            val responseReceived = CompletableDeferred<JsonObject>()

            launch {
                for (message in incoming) {
                    when (message) {
                        is Frame.Text -> {
                            println("Received Text Frame: ${message.readText()}")
                            val responseJson = Json.parseToJsonElement(message.readText()) as JsonObject

                            if (responseJson["type"]?.jsonPrimitive?.content == "response.done") {
                                responseReceived.complete(responseJson)
                            }
                        }

                        is Frame.Binary -> {}

                        is Frame.Ping -> {}

                        is Frame.Pong -> {}

                        is Frame.Close -> {}
                    }
                }
            }


            val conversationItemEvent = ConversationItemEvent(
                type = "conversation.item.create",
                item = Item(
                    type = "message",
                    role = "user",
                    content = listOf(
                        Content(
                            type = "input_text",
                            text = message
                        )
                    )
                )
            )

            send(
                Frame.Text(
                    Json.encodeToString<ConversationItemEvent>(conversationItemEvent)
                )
            )

            val responseEvent = ResponseEvent(
                type = "response.create",
                response = Response(
                    modalities = listOf("text")
                )
            )

            send(
                Frame.Text(
                    Json.encodeToString(responseEvent)
                )
            )

            withTimeout(10000) {
                response = responseReceived.await()
            }
        }

        client.close()
    }

    return response
}

@Serializable
data class ConversationItemEvent(
    val type: String,
    val item: Item
)

@Serializable
data class Item(
    val type: String,
    val role: String,
    val content: List<Content>
)

@Serializable
data class Content(
    val type: String,
    val text: String
)

class Audio {
    companion object {
        @Serializable
        data class ConversationItemEvent(
            val type: String,
            val item: Item
        )

        @Serializable
        data class Item(
            val type: String,
            val role: String,
            val content: List<Content>
        )

        @Serializable
        data class Content(
            val type: String,
            val audio: String
        )
    }
}

@Serializable
data class ResponseEvent(
    val type: String,
    val response: Response
)

@Serializable
data class Response(
    val modalities: List<String>
)

fun realtimeAudioApi(modelId: String, filePath: String): String {
    val client = HttpClient(CIO) {
        install(WebSockets)
    }

    val audioData = StringBuilder()
    var response: JsonObject? = null

    runBlocking {
        client.webSocket(
            host = LITELLM_HOST,
            path = "realtime",
            request = {
                url.parameters.append("model", modelId)
                header(HttpHeaders.Authorization, "Bearer $LITELLM_API_KEY")
                header("OpenAI-Beta", "realtime=v1")
            },
        ) {
            val responseReceived = CompletableDeferred<JsonObject>()

            launch {
                for (message in incoming) {
                    when (message) {
                        is Frame.Text -> {
                            println("Received Text Frame: ${message.readText()}")
                            val responseJson = Json.parseToJsonElement(message.readText()) as JsonObject

                            if (responseJson["type"]?.jsonPrimitive?.content == "response.audio.delta") {
                                audioData.append(responseJson["delta"]?.jsonPrimitive?.content ?: "")
                            }

                            if (responseJson["type"]?.jsonPrimitive?.content == "response.done") {
                                responseReceived.complete(responseJson)
                            }
                        }

                        is Frame.Binary -> {}

                        is Frame.Ping -> {}

                        is Frame.Pong -> {}

                        is Frame.Close -> {}
                    }
                }
            }

            val audioMessage = encodePCMToBase64(filePath)

            val conversationItemEvent = Audio.Companion.ConversationItemEvent(
                type = "conversation.item.create",
                item = Audio.Companion.Item(
                    type = "message",
                    role = "user",
                    content = listOf(
                        Audio.Companion.Content(
                            type = "input_audio",
                            audio = audioMessage
                        )
                    )
                )
            )

            send(
                Frame.Text(
                    Json.encodeToString<Audio.Companion.ConversationItemEvent>(conversationItemEvent)
                )
            )

            val responseEvent = ResponseEvent(
                type = "response.create",
                response = Response(
                    modalities = listOf("audio", "text")
                )
            )

            send(
                Frame.Text(
                    Json.encodeToString(responseEvent)
                )
            )

            withTimeout(10000) {
                response = responseReceived.await()
            }
        }

        client.close()
    }

    return audioData.toString()
}

fun encodePCMToBase64(resourcePath: String): String {
    val classLoader = Thread.currentThread().contextClassLoader
    val audioFile = classLoader.getResource(resourcePath)?.file?.let { File(it) }
        ?: error("Could not find image at $resourcePath")

    // Read the MP3 file as bytes
    val fileBytes = audioFile.readBytes()

    // Encode the file bytes to a Base64 string
    return Base64.getEncoder().encodeToString(fileBytes)
}

