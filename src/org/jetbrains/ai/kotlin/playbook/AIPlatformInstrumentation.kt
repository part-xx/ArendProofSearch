package org.example.org.jetbrains.ai.kotlin.playbook

import io.ktor.client.plugins.api.*
import io.ktor.util.*
import io.ktor.utils.io.*
import io.opentelemetry.api.GlobalOpenTelemetry
import io.opentelemetry.api.trace.Span
import io.opentelemetry.context.Scope
import io.opentelemetry.semconv.incubating.GenAiIncubatingAttributes.*
import kotlinx.io.readByteArray
import kotlinx.serialization.json.*


private const val MESSAGE_PLACEHOLDER = "Message content is hidden"

class OpenTelemetryPluginConfig {
    var logBody = true
}

val OpenTelemetryPlugin = createClientPlugin("OpenTelemetryPlugin", ::OpenTelemetryPluginConfig) {
    val tracer = GlobalOpenTelemetry.getTracer(AI_DEVELOPMENT_KIT_TRACER)
    val spanKey = AttributeKey<Span>("OtelSpan")
    val scopeKey = AttributeKey<Scope>("OtelScope")

    onRequest { request, _ ->
        if (request.url.toString().endsWith(".json") || request.url.toString().endsWith("/ping")) {
            return@onRequest
        }

        val span = tracer.spanBuilder("AI Platform-generation").startSpan()
        val scope = span.makeCurrent()

        span.setAttribute(GEN_AI_SYSTEM, "JetBrains AI Platform")

        request.attributes.put(spanKey, span)
        request.attributes.put(scopeKey, scope)

        getRequestBodyAttributes(
            span,
            Json.decodeFromString<JsonObject>(request.body.toString()),
            this@createClientPlugin.pluginConfig.logBody
        )
    }

    transformResponseBody { response, content, requestedType ->
        if (requestedType.type != ByteReadChannel::class) return@transformResponseBody content

        val span = response.call.attributes.getOrNull(spanKey) ?: return@transformResponseBody content
        val scope = response.call.attributes.getOrNull(scopeKey) ?: return@transformResponseBody content

        val receivedContent = content.readRemaining().readByteArray().decodeToString()

        getResponseBodyAttributes(span, receivedContent, this@createClientPlugin.pluginConfig.logBody)

        scope.close()
        span.end()

        return@transformResponseBody ByteReadChannel(receivedContent)
    }
}

private fun getRequestBodyAttributes(span: Span, body: JsonObject, logBody: Boolean) {
    body["temperature"]?.let { span.setAttribute(GEN_AI_REQUEST_TEMPERATURE, it.jsonPrimitive.content.toDouble()) }
    body["profile"]?.let { span.setAttribute(GEN_AI_REQUEST_MODEL, it.jsonPrimitive.content) }

    body["chat"]?.jsonObject["messages"]?.let {
        for ((index, message) in it.jsonArray.withIndex()) {
            span.setAttribute("gen_ai.prompt.$index.role", message.jsonObject["type"]?.jsonPrimitive?.content)
            span.setAttribute(
                "gen_ai.prompt.$index.content",
                if (logBody) {
                    message.jsonObject["content"]?.jsonPrimitive?.content
                } else {
                    MESSAGE_PLACEHOLDER
                }
            )
        }
    }
}

private fun getResponseBodyAttributes(span: Span, body: String, logBody: Boolean) {
    val eventList = body
        .split(Regex("""\r?\n\r?\n"""))
        .mapNotNull { line ->
            line.trim()
                .removePrefix("data: ")
                .takeIf { it.isNotBlank() }
        }
        .mapNotNull { jsonString: String ->
            try {
                Json.parseToJsonElement(jsonString).jsonObject
            } catch (_: IllegalArgumentException) {
                null
            }
        }

    val content = mutableListOf<String>()

    eventList.forEach { event ->
        val type = event["type"]?.jsonPrimitive?.content
        if (type == "Content") {
            content.add(event["content"]?.jsonPrimitive?.content ?: "")
        }
        if (type == "FinishMetadata") {
            event["reason"]?.jsonPrimitive?.content?.let { span.setAttribute("gen_ai.completion.0.finish_reason", it) }
        }
        if (type == "QuotaMetadata") {
            event["spent"]?.jsonObject["amount"]?.jsonPrimitive?.content?.let { span.setAttribute("gen_ai.spent", it) }
            event["spent"]?.jsonObject["amount"]?.jsonPrimitive?.content?.let { span.setAttribute("costDetails.total", it) }
        }
    }

    span.setAttribute("gen_ai.completion.0.role", "assistant")
    span.setAttribute(
        "gen_ai.completion.0.content",
        if (logBody) {
            content.joinToString("") { it }
        } else {
            MESSAGE_PLACEHOLDER
        }
    )
}