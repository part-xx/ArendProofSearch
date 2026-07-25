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

    private class CLIOutput(val result: String, val errors: String)

    private fun invokeCliCommand(vararg args: String): CLIOutput {
        val output = StringBuilder()
        val errors = StringBuilder()

        val exitCode = client.invoke("cli", mapOf("args" to args.toList())) { frame ->
            /*val frameStr = frame.getOrDefault("data", "").toString()
            if (frameStr.startsWith("[ERROR]")) {
                errors.append(frameStr)
            } else {
                output.append(frameStr)
            }*/
            when (frame["kind"]) {
                "stdout" -> output.append(frame.getOrDefault("data", ""))
                "stderr" -> errors.append(frame.getOrDefault("data", ""))
            }
        }

        if (exitCode != 0) {
            if (errors.trim().isEmpty()) {
                throw IOException("Daemon command failed (exit $exitCode)")
            }
            // return CLIOutput("", errors.toString().trim())
        }



        return CLIOutput(output.toString().trim(), errors.toString().trim())
    }

    private fun extractJson(raw: String): String {
        val start = raw.lastIndexOf("\n{")
        if (start >= 0) return raw.substring(start + 1).trim()
        if (raw.startsWith("{\"")) return raw.trim()
        throw IOException("No JSON object in daemon output: ${raw.take(200)}")
    }

    override fun findGoals(moduleDef: String): FindGoalsResponse {
        val cliOutput = invokeCliCommand("-fg", moduleDef)
        return json.decodeFromString<FindGoalsResponse>(extractJson(cliOutput.result))
    }

    override fun applyStep(moduleDef: String, fullBody: String): ApplyStepResponse {
        val cliOutput = invokeCliCommand("-as", moduleDef, fullBody)
        return json.decodeFromString<ApplyStepResponse>(extractJson(cliOutput.result))
    }

    override fun getScope(moduleDef: String, goalId: String): ScopeResponse {
        val cliOutput = invokeCliCommand("-gs", moduleDef, goalId)
        return json.decodeFromString<ScopeResponse>(extractJson(cliOutput.result))
    }

    override fun proofSearch(pattern: String): ProofSearchResponse {
        val cliOutput = invokeCliCommand("-psj", pattern)
        return json.decodeFromString<ProofSearchResponse>(extractJson(cliOutput.result))
    }

    override fun signature(moduleDef: String): String {
        val cliOutput = invokeCliCommand("-sg", moduleDef)
        return cliOutput.result.lines().last { it.isNotBlank() }
    }

    override fun signatureInfo(moduleDef: String, name: String): SignatureInfoResponse? {
        return try {
            val cliOutput = invokeCliCommand("-si", moduleDef, name)
            json.decodeFromString<SignatureInfoResponse>(extractJson(cliOutput.result))
        } catch (_: Exception) {
            null
        }
    }

    override fun typeExpr(moduleDef: String, goalId: String, expression: String): TypeExprResponse? {
        return try {
            val cliOutput = invokeCliCommand("-te", moduleDef, goalId, "\"$expression\"")
            if (cliOutput.errors.isNotEmpty()) {
                return TypeExprResponse(null, cliOutput.errors)
            }
            TypeExprResponse(json.decodeFromString<TypeExprData>(extractJson(cliOutput.result)))
        } catch (_: Exception) {
            null
        }
    }

    override fun close() {
        client.close()
    }
}
