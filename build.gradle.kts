plugins {
    kotlin("jvm") version "2.2.0"
}

// val projectArend = gradle.includedBuild("Arend")
group = "org.arend.lang"
version = "1.11.0.3"

repositories {
    mavenCentral()
}

dependencies {
    implementation("org.arend:parser")
    implementation("org.antlr:antlr4-runtime:4.10")
    implementation("ai.koog:koog-agents:0.6.0")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.7.3")
    implementation("org.json:json:20231013")
    implementation(kotlin("reflect"))
    implementation(kotlin("stdlib-jdk8"))
    implementation("org.arend:base")
    implementation("org.arend:cli")
    implementation("org.apache.commons:commons-lang3:3.12.0")
    implementation("commons-cli:commons-cli:1.5.0")
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
}

