package typechecker.cli

import kotlinx.serialization.json.Json
import java.io.IOException
import java.nio.file.Path
import java.nio.file.Paths

class CliProcessApi(
    private val libraryPath: Path,
    private val jarPath: Path = Paths.get(
        System.getProperty("arend.jar",
            "/Users/admin/codingspace/arend-lang-new/Arend/cli/build/libs/cli-1.11.0-full.jar")
    )
) : CliApi, AutoCloseable {

    private val json = Json { ignoreUnknownKeys = true }

    private fun runCli(vararg extraArgs: String): String {
        val cmd = mutableListOf("java", "-jar", jarPath.toString())
        val libsDir = libraryPath.resolve("libs")
        if (java.nio.file.Files.isDirectory(libsDir)) {
            cmd.addAll(listOf("-L", libsDir.toString()))
        }
        cmd.addAll(extraArgs)
        cmd.add(libraryPath.toString())

        val process = ProcessBuilder(cmd)
            .directory(libraryPath.toFile())
            .redirectErrorStream(false)
            .start()

        val stdout = process.inputStream.bufferedReader().readText()
        val stderr = process.errorStream.bufferedReader().readText()
        val exitCode = process.waitFor()

        if (exitCode != 0 && stdout.isBlank()) {
            throw IOException("CLI command failed (exit $exitCode): $stderr\ncmd: ${cmd.joinToString(" ")}")
        }

        return stdout.trim()
    }

    private fun extractJson(raw: String): String {
        // Find the last JSON object in output — earlier '{' may come from
        // non-JSON text like "{?}" in goal pretty-printing.
        val start = raw.lastIndexOf("\n{")
        if (start >= 0) return raw.substring(start + 1).trim()
        // Fallback: output starts with JSON
        if (raw.startsWith("{\"")) return raw.trim()
        throw IOException("No JSON object in CLI output: $raw")
    }

    override fun findGoals(moduleDef: String): FindGoalsResponse {
        val raw = runCli("-fg", moduleDef)
        return json.decodeFromString<FindGoalsResponse>(extractJson(raw))
    }

    override fun checkExpression(moduleDef: String, goalId: String, expression: String): CheckResult {
        val raw = runCli("-ce", moduleDef, goalId, expression)
        return json.decodeFromString<CheckResult>(extractJson(raw))
    }

    override fun applyStep(moduleDef: String, goalId: String, expression: String): ApplyStepResponse {
        val raw = runCli("-as", moduleDef, goalId, expression)
        return json.decodeFromString<ApplyStepResponse>(extractJson(raw))
    }

    override fun getScope(moduleDef: String, goalId: String): ScopeResponse {
        val raw = runCli("--json", "-sc", moduleDef)
        val scopeJson = json.decodeFromString<CliScopeResponse>(extractJson(raw))
        return ScopeResponse(
            scope = scopeJson.scope.map { ScopeEntry(name = it.name, kind = it.kind ?: "", type = "") },
            locals = emptyList()
        )
    }

    override fun proofSearch(pattern: String): ProofSearchResponse {
        val raw = runCli("--json", "-ps", pattern)
        return json.decodeFromString<ProofSearchResponse>(extractJson(raw))
    }

    override fun close() {}
}

@kotlinx.serialization.Serializable
private data class CliScopeEntry(
    val name: String,
    val library: String? = null,
    val module: String? = null,
    val longName: String? = null,
    val kind: String? = null
)

@kotlinx.serialization.Serializable
private data class CliScopeResponse(
    val target: String = "",
    val scope: List<CliScopeEntry> = emptyList(),
    val count: Int = 0
)
