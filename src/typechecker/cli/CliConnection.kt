package typechecker.cli

import kotlinx.serialization.json.Json
import org.arend.frontend.cli.daemon.DaemonPaths
import org.arend.frontend.cli.daemon.LockFile
import org.arend.frontend.cli.daemon.client.DaemonClient
import org.arend.frontend.cli.daemon.server.SocketBinder
import java.io.IOException
import java.nio.file.Path

class CliConnection(libraryPath: Path) : CliApi, AutoCloseable {
    private val client: DaemonClient
    private val json = Json { ignoreUnknownKeys = true }

    init {
        val paths = DaemonPaths.resolve(libraryPath)
            ?: throw IOException("Could not resolve library at $libraryPath")

        val lockFile = LockFile.read(paths.lockFile).orElse(null)
            ?: throw IOException("No daemon running for library at $libraryPath (no lock file at ${paths.lockFile})")

        if (lockFile.socketPath.isNullOrEmpty()) {
            throw IOException("Daemon at PID ${lockFile.pid} has no socket bound")
        }

        if (ProcessHandle.of(lockFile.pid).isEmpty) {
            LockFile.deleteQuietly(paths.lockFile)
            throw IOException("Daemon at PID ${lockFile.pid} is dead (stale lock file cleaned up)")
        }

        val addr = SocketBinder.parseAddress(lockFile.socketPath)
        client = DaemonClient.connect(addr)
    }

    private fun invokeCliCommand(vararg args: String): String {
        val output = StringBuilder()
        val errors = StringBuilder()

        val exitCode = client.invoke("cli", mapOf("args" to args.toList())) { frame ->
            when (frame["kind"]) {
                "stdout" -> output.append(frame.getOrDefault("data", ""))
                "stderr" -> errors.append(frame.getOrDefault("data", ""))
            }
        }

        if (exitCode != 0 && output.isEmpty()) {
            throw IOException("Daemon command failed (exit $exitCode): $errors")
        }

        return output.toString().trim()
    }

    override fun findGoals(moduleDef: String): FindGoalsResponse {
        val raw = invokeCliCommand("-fg", moduleDef)
        return json.decodeFromString<FindGoalsResponse>(raw)
    }

    override fun checkExpression(moduleDef: String, goalId: String, expression: String): CheckResult {
        val raw = invokeCliCommand("-ce", moduleDef, goalId, expression)
        return json.decodeFromString<CheckResult>(raw)
    }

    override fun applyStep(moduleDef: String, goalId: String, expression: String): ApplyStepResponse {
        val raw = invokeCliCommand("-as", moduleDef, goalId, expression)
        return json.decodeFromString<ApplyStepResponse>(raw)
    }

    override fun getScope(moduleDef: String, goalId: String): ScopeResponse {
        val raw = invokeCliCommand("-gs", moduleDef, goalId)
        return json.decodeFromString<ScopeResponse>(raw)
    }

    override fun proofSearch(pattern: String): ProofSearchResponse {
        val raw = invokeCliCommand("-psj", pattern)
        return json.decodeFromString<ProofSearchResponse>(raw)
    }

    override fun close() {
        client.close()
    }
}
