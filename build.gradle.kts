plugins {
    kotlin("jvm") version "2.2.0"
    kotlin("plugin.serialization") version "2.2.0"
    application
}

// val projectArend = gradle.includedBuild("Arend")
group = "org.arend.lang"
version = "1.11.0.3"

val ktorVersion: String by project
val openaiVersion: String by project
val logbackVersion: String by project
val otelVersion: String by project
val otelSemconvIncubatingVersion: String by project
val koogVersion: String by project

repositories {
  mavenCentral()
 // maven("https://packages.jetbrains.team/maven/p/grazi/grazie-platform-public/")
//  maven("https://packages.jetbrains.team/maven/p/ai-development-kit/ai-development-kit")
}

dependencies {
  testImplementation(kotlin("test"))
  implementation(kotlin("stdlib"))
    implementation("org.arend:parser")
    implementation("org.antlr:antlr4-runtime:4.10")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.7.3")
    implementation("org.json:json:20231013")
    implementation(kotlin("reflect"))
    implementation(kotlin("stdlib-jdk8"))
    implementation("org.arend:base")
    implementation("org.arend:cli")
    implementation("org.apache.commons:commons-lang3:3.12.0")
    implementation("commons-cli:commons-cli:1.5.0")

  implementation("com.openai:openai-java:$openaiVersion")
  implementation("com.squareup.okhttp3:okhttp:4.12.0")
  implementation("io.ktor:ktor-client-core:$ktorVersion")
  implementation("io.ktor:ktor-client-cio:$ktorVersion")
  implementation("io.ktor:ktor-client-logging:$ktorVersion")
  implementation("io.ktor:ktor-client-websockets:$ktorVersion")
  implementation("io.ktor:ktor-client-content-negotiation:$ktorVersion")
  implementation("io.ktor:ktor-serialization-kotlinx-json:$ktorVersion")
  implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.8.1")
  implementation("ch.qos.logback:logback-classic:$logbackVersion")

  implementation("io.opentelemetry:opentelemetry-api:${otelVersion}")
  implementation("io.opentelemetry:opentelemetry-sdk:${otelVersion}")
  implementation("io.opentelemetry:opentelemetry-exporter-otlp:${otelVersion}")
  implementation("io.opentelemetry:opentelemetry-exporter-logging:${otelVersion}")
  implementation("io.opentelemetry.semconv:opentelemetry-semconv-incubating:${otelSemconvIncubatingVersion}")

  // JetBrains AI Platform and koog dependencies - commented out for build
  // Uncomment later if you need JetBrains integration
  //implementation("com.jetbrains:ai-dev-kit-tracing-core:0.0.21")
  //implementation("com.jetbrains:ai-dev-kit-tracing-openai:0.0.21")
  //implementation("ai.grazie.api:api-gateway-client-jvm:0.8.2")
  //implementation("ai.grazie.client:client-ktor-jvm:0.8.2")
  //implementation("ai.koog:koog-agents:$koogVersion")

  testImplementation("io.opentelemetry:opentelemetry-sdk-testing:${otelVersion}")
}

kotlin {
  jvmToolchain(21)
}

application {
  mainClass.set("MainKt")
}

sourceSets {
  main {
    java {
      setSrcDirs(listOf("src"))
    }
    resources {
      setSrcDirs(listOf("resources"))
    }
  }
  test {
    java {
      setSrcDirs(listOf("test"))
    }
  }
}

val litellmApiKey: String by project
val llmBaseUrl: String by project
val llmApiKey: String by project
val llmModel: String by project
val openaiLikeApiKey: String by project
val openaiLikeBaseUrl: String by project
val openaiLikeModel: String by project
val llmBackend = providers.gradleProperty("llmBackend").orElse("local")
val llmRegime = providers.gradleProperty("llmRegime").orElse("qwen3-direct-v1")
val llmCandidateMode = providers.gradleProperty("llmCandidateMode").orElse("batch")
val arendLibPath = providers.gradleProperty("arendLibPath").orElse("")
val localModelPath = providers.gradleProperty("localModelPath")
  .orElse("../VM_setup/models/qwen3-coder-30b-a3b-arend-direct-v1-production-20260823-001-q5_k_m.gguf")
val llamaServerExecutable = providers.gradleProperty("llamaServerExecutable").orElse("llama-server")
val localContextSize = providers.gradleProperty("localContextSize").orElse("8192")
val localMaxTokens = providers.gradleProperty("localMaxTokens").orElse("512")
val localStartupTimeoutSeconds = providers.gradleProperty("localStartupTimeoutSeconds").orElse("180")
val llmMaxAttempts = providers.gradleProperty("llmMaxAttempts").orElse("10")
val llmMaxCandidates = providers.gradleProperty("llmMaxCandidates").orElse("2")
val llmBatchTemperature = providers.gradleProperty("llmBatchTemperature").orElse("0.7")
val llmPremisesFile = providers.gradleProperty("llmPremisesFile").orElse("")

tasks.test {
  useJUnitPlatform()
  maxHeapSize = "8g"
  // Proof-search benchmark (BenchmarkTest): -Pbench=true [-Pbench.modules=Bench_A,Bench_B] [-Pbench.limit=N]
  for (property in listOf("bench", "bench.modules", "bench.names", "bench.limit", "bench.log", "bench.expansions", "bench.seconds", "proofsearch.debug", "proofsearch.timing", "proofsearch.noTermMemo", "proofsearch.noResolveMemo", "proofsearch.verifyTermMemo")) {
    providers.gradleProperty(property).orNull?.let { systemProperty(property, it) }
  }
  environment("LITELLM_API_KEY", System.getenv("LITELLM_API_KEY") ?: litellmApiKey)
  systemProperty("llm.base.url", llmBaseUrl)
  systemProperty("llm.api.key", llmApiKey.ifEmpty { litellmApiKey })
  systemProperty("llm.model", llmModel)
  environment("OPENAI_LIKE_API_KEY", System.getenv("OPENAI_LIKE_API_KEY") ?: openaiLikeApiKey)
  systemProperty("openai.like.base.url", openaiLikeBaseUrl)
  systemProperty("openai.like.model", openaiLikeModel)
  systemProperty("llm.backend", llmBackend.get())
  systemProperty("llm.regime", llmRegime.get())
  systemProperty("llm.candidate.mode", llmCandidateMode.get())
  systemProperty("arend.lib.path", arendLibPath.get())
  systemProperty("local.model.path", localModelPath.get())
  systemProperty("local.llama.server.executable", llamaServerExecutable.get())
  systemProperty("local.context.size", localContextSize.get())
  systemProperty("local.max.tokens", localMaxTokens.get())
  systemProperty("local.startup.timeout.seconds", localStartupTimeoutSeconds.get())
  systemProperty("llm.max.attempts", llmMaxAttempts.get())
  systemProperty("llm.max.candidates", llmMaxCandidates.get())
  systemProperty("llm.batch.temperature", llmBatchTemperature.get())
  systemProperty("llm.premises.file", llmPremisesFile.get())
}

tasks.withType<JavaExec>().configureEach {
  systemProperty("openai.like.api.key", openaiLikeApiKey)
  systemProperty("openai.like.base.url", openaiLikeBaseUrl)
  systemProperty("openai.like.model", openaiLikeModel)
  systemProperty("llm.backend", llmBackend.get())
  systemProperty("llm.regime", llmRegime.get())
  systemProperty("llm.candidate.mode", llmCandidateMode.get())
  systemProperty("local.model.path", localModelPath.get())
  systemProperty("local.llama.server.executable", llamaServerExecutable.get())
  systemProperty("local.context.size", localContextSize.get())
  systemProperty("local.max.tokens", localMaxTokens.get())
  systemProperty("local.startup.timeout.seconds", localStartupTimeoutSeconds.get())
  systemProperty("llm.max.attempts", llmMaxAttempts.get())
  systemProperty("llm.max.candidates", llmMaxCandidates.get())
  systemProperty("llm.batch.temperature", llmBatchTemperature.get())
  systemProperty("llm.premises.file", llmPremisesFile.get())
}
