plugins {
    kotlin("jvm") version "2.2.0"
    kotlin("plugin.serialization") version "2.2.0"
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
  maven("https://packages.jetbrains.team/maven/p/grazi/grazie-platform-public/")
  maven("https://packages.jetbrains.team/maven/p/ai-development-kit/ai-development-kit")
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
  implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.8.1")
  implementation("ch.qos.logback:logback-classic:$logbackVersion")

  implementation("io.opentelemetry:opentelemetry-api:${otelVersion}")
  implementation("io.opentelemetry:opentelemetry-sdk:${otelVersion}")
  implementation("io.opentelemetry:opentelemetry-exporter-otlp:${otelVersion}")
  implementation("io.opentelemetry:opentelemetry-exporter-logging:${otelVersion}")
  implementation("io.opentelemetry.semconv:opentelemetry-semconv-incubating:${otelSemconvIncubatingVersion}")

  implementation("com.jetbrains:ai-dev-kit-tracing-core:0.0.21")
  implementation("com.jetbrains:ai-dev-kit-tracing-openai:0.0.21")

  implementation("ai.grazie.api:api-gateway-client-jvm:0.8.2")
  implementation("ai.grazie.client:client-ktor-jvm:0.8.2")

  implementation("ai.koog:koog-agents:$koogVersion")

  testImplementation("io.opentelemetry:opentelemetry-sdk-testing:${otelVersion}")
}

kotlin {
  jvmToolchain(21)
}

sourceSets {
  main {
    java {
      setSrcDirs(listOf("src"))
    }
  }
  test {
    java {
      setSrcDirs(listOf("test"))
    }
  }
}

val litellmApiKey: String by project

tasks.test {
  useJUnitPlatform()
  maxHeapSize = "4g"
  environment("LITELLM_API_KEY", System.getenv("LITELLM_API_KEY") ?: litellmApiKey)
}

