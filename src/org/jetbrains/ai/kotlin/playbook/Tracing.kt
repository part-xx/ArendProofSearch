package org.example.org.jetbrains.ai.kotlin.playbook

import io.opentelemetry.api.common.AttributeKey
import io.opentelemetry.api.common.Attributes
import io.opentelemetry.exporter.logging.LoggingSpanExporter
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.resources.Resource
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.SdkTracerProviderBuilder
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor
import io.opentelemetry.sdk.trace.export.SpanExporter
import java.util.Base64
import java.util.concurrent.TimeUnit

const val AI_DEVELOPMENT_KIT_TRACER = "ai-development-kit"

fun initOpenTelemetry(
    langfuseUrl: String,
    langfusePublicKey: String,
    langfuseSecretKey: String,
    traceToConsole: Boolean = false,
): SdkTracerProvider {
    val resource = Resource.getDefault()
        .merge(
            Resource.create(
                Attributes.of(AttributeKey.stringKey("service.name"), "ai-development-kit")
            )
        )

    val tracerProvider = SdkTracerProvider.builder()
        .setResource(resource)
        .addLangfuseSpanProcessor(langfuseUrl, langfusePublicKey, langfuseSecretKey)
        .apply {
            if (traceToConsole) {
                addLoggingSpanProcessor()
            }
        }
        .build()

    val openTelemetry = OpenTelemetrySdk.builder()
        .setTracerProvider(tracerProvider)
        .buildAndRegisterGlobal()

    val sdk = openTelemetry
    Runtime.getRuntime().addShutdownHook(Thread {
        sdk.sdkTracerProvider.shutdown()
    })

    return tracerProvider
}

fun SdkTracerProviderBuilder.addLoggingSpanProcessor(): SdkTracerProviderBuilder {
    val spanExporter = LoggingSpanExporter.create()
    addSpanProcessor(SimpleSpanProcessor.create(spanExporter))
    return this
}

fun SdkTracerProviderBuilder.addLangfuseSpanProcessor(
    langfuseUrl: String,
    langfusePublicKey: String,
    langfuseSecretKey: String,
): SdkTracerProviderBuilder {
    val credentials = "$langfusePublicKey:$langfuseSecretKey"
    val auth = Base64.getEncoder().encodeToString(credentials.toByteArray(Charsets.UTF_8))

    val langfuseSpanExporter = OtlpHttpSpanExporter.builder()
        .setTimeout(30, TimeUnit.SECONDS)
        .setEndpoint("$langfuseUrl/api/public/otel/v1/traces")
        .addHeader("Authorization", "Basic $auth")
        .build()

    addSpanProcessor(
        BatchSpanProcessor.builder(langfuseSpanExporter)
            .setScheduleDelay(3, TimeUnit.SECONDS)
            .build()
    )
    return this
}

fun SdkTracerProviderBuilder.addWeaveSpanProcessor(
): SdkTracerProviderBuilder {
    val weaveSpanExporter = createWeaveSpanExporter(
        "https://trace.wandb.ai",
        System.getenv()["WEAVE_ENTITY"] ?: throw IllegalArgumentException("WEAVE_ENTITY is not set"),
        System.getenv()["WEAVE_PROJECT_NAME"] ?: "koog-tracing",
        System.getenv()["WEAVE_API_KEY"] ?: throw IllegalArgumentException("WEAVE_API_KEY is not set")
    )

    addSpanProcessor(
        BatchSpanProcessor.builder(weaveSpanExporter)
            .setScheduleDelay(3, TimeUnit.SECONDS)
            .build()
    )
    return this
}

private fun createWeaveSpanExporter(
    weaveOtelUrl: String,
    entity: String,
    projectName: String,
    apiKey: String,
): SpanExporter {
    val auth = Base64.getEncoder().encodeToString("api:$apiKey".toByteArray(Charsets.UTF_8))

    return OtlpHttpSpanExporter.builder()
        .setTimeout(30, TimeUnit.SECONDS)
        .setEndpoint("$weaveOtelUrl/otel/v1/traces")
        .addHeader("project_id", "$entity/$projectName")
        .addHeader("Authorization", "Basic $auth")
        .build()
}

