package typechecker.cli

import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonArray
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.JsonPrimitive
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.apache.commons.cli.ParseException
import search.best_first.BestFirstSearch
import typechecker.LLMClient
import typechecker.LocalLlamaLLMClient
import typechecker.OpenAILikeLLMClient
import typechecker.cli.proofstep.CandidateGenerationMode
import typechecker.cli.proofstep.CliLLMStepGenerator
import typechecker.cli.proofstep.TacticPromptFormat
import typechecker.cli.proofstep.openaiLikeApiKey
import typechecker.cli.proofstep.openaiLikeBaseUrl
import typechecker.cli.proofstep.openaiLikeEnableThinking
import typechecker.cli.proofstep.openaiLikeMaxTokens
import typechecker.cli.proofstep.openaiLikeModel
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

// LLM dependencies - commented out for build
// Uncomment later to use JetBrains/koog or other LLM backend
//import org.jetbrains.ai.kotlin.playbook.LLM_MODEL_ID

enum class LLMBackend {
    LOCAL,
    REMOTE;

    companion object {
        fun parse(value: String): LLMBackend? = when (value.lowercase()) {
            "local" -> LOCAL
            "remote" -> REMOTE
            else -> null
        }
    }
}

internal fun parsePromptRegime(value: String): TacticPromptFormat? = when (value.lowercase()) {
    "fine-tuned", "finetuned", "fine" -> TacticPromptFormat.FINE_TUNED_AREND
    "qwen3-direct-v1", "qwen3-direct", "direct-v1" -> TacticPromptFormat.QWEN3_DIRECT_V1
    "instruction", "general" -> TacticPromptFormat.INSTRUCTION
    else -> null
}

internal fun defaultPromptRegime(backend: LLMBackend): TacticPromptFormat = when (backend) {
    LLMBackend.LOCAL -> TacticPromptFormat.INSTRUCTION
    LLMBackend.REMOTE -> TacticPromptFormat.INSTRUCTION
}

internal fun parseCandidateMode(value: String): CandidateGenerationMode? =
    CandidateGenerationMode.parse(value)

internal fun defaultCandidateMode(promptFormat: TacticPromptFormat): CandidateGenerationMode =
    if (promptFormat == TacticPromptFormat.QWEN3_DIRECT_V1) {
        CandidateGenerationMode.BATCH
    } else {
        CandidateGenerationMode.ITERATIVE_FEEDBACK
    }

internal fun promptRegimeName(promptFormat: TacticPromptFormat): String = when (promptFormat) {
    TacticPromptFormat.INSTRUCTION -> "instruction"
    TacticPromptFormat.FINE_TUNED_AREND -> "fine-tuned"
    TacticPromptFormat.QWEN3_DIRECT_V1 -> "qwen3-direct-v1"
}

/** Loads either a JSON string array or a dataset-style object containing `Premises`. */
internal fun loadPremises(path: Path): List<String> {
    require(Files.isRegularFile(path)) { "Premises file not found: ${path.toAbsolutePath().normalize()}" }
    val root = Json.parseToJsonElement(Files.readString(path))
    val values = when (root) {
        is JsonArray -> root
        is JsonObject -> (root["Premises"] ?: root["premises"]) as? JsonArray
            ?: throw IllegalArgumentException("Premises JSON object must contain an array field named 'Premises'")
        else -> throw IllegalArgumentException("Premises file must contain a JSON array or object")
    }
    return values.mapIndexed { index, value ->
        val primitive = value as? JsonPrimitive
        require(primitive != null && primitive.isString) {
            "Premises[$index] must be a JSON string"
        }
        primitive.content
    }
}

fun runCliSearch(args: Array<String>) {
    val cmdOptions = Options()
    cmdOptions.addOption(
        Option.builder("L").longOpt("libdir").hasArg().argName("dir")
            .desc("directory containing the library (with arend.yaml)").build()
    )
    cmdOptions.addOption(
        Option.builder("m").longOpt("module-def").hasArg().argName("MODULE:DEF")
            .desc("module and definition to search (e.g., testPS:myTheorem)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("model").hasArg().argName("model-id")
            .desc("remote OpenAI-compatible model ID (default: OPENAI_LIKE_MODEL)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("llm").hasArg().argName("local|remote")
            .desc("LLM backend (default: AREND_LLM_BACKEND or remote)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("regime").hasArg().argName("qwen3-direct-v1|fine-tuned|instruction")
            .desc("prompt regime (default: configured llmRegime, otherwise instruction)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("candidate-mode").hasArg().argName("iterative|batch")
            .desc("candidate generation: iterative checker feedback or one multi-completion request (direct-v1 defaults to batch)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("local-model")
            .desc("compatibility alias for --llm local").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("local-model-path").hasArg().argName("gguf")
            .desc("local GGUF path (also enables --local-model; default: ../VM_setup/models/${LocalLlamaLLMClient.DEFAULT_MODEL_FILENAME})").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("llama-server").hasArg().argName("executable")
            .desc("llama-server executable (default: LLAMA_SERVER or llama-server)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("local-context-size").hasArg().argName("tokens")
            .desc("llama.cpp context tokens per completion (default: ${LocalLlamaLLMClient.DEFAULT_CONTEXT_SIZE})").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("local-max-tokens").hasArg().argName("tokens")
            .desc("maximum generated tactic tokens (default: ${LocalLlamaLLMClient.DEFAULT_MAX_TOKENS})").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("local-startup-timeout-seconds").hasArg().argName("seconds")
            .desc("local llama-server startup timeout").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("max-attempts").hasArg().argName("count")
            .desc("raw proposal budget (default: ${CliLLMStepGenerator.DEFAULT_MAX_ATTEMPTS})").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("max-candidates").hasArg().argName("count")
            .desc("validated candidates retained per goal (default: ${CliLLMStepGenerator.DEFAULT_MAX_CANDIDATES})").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("batch-temperature").hasArg().argName("temperature")
            .desc("sampling temperature for batch completions (default: ${CliLLMStepGenerator.DEFAULT_BATCH_TEMPERATURE})").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("premises-file").hasArg().argName("json")
            .desc("JSON array, or dataset object with a Premises array, for the tactic prompt").build()
    )

    val cmdLine = try {
        DefaultParser().parse(cmdOptions, args)
    } catch (e: ParseException) {
        System.err.println(e.message)
        return
    }

    val libPath = cmdLine.getOptionValue("L")
        ?: run { System.err.println("Missing required option: -L <libdir>"); return }
    val moduleDef = cmdLine.getOptionValue("m")
        ?: run { System.err.println("Missing required option: --module-def MODULE:DEF"); return }

    fun configuredValue(option: String, environment: String, property: String): String? =
        cmdLine.getOptionValue(option)
            ?: System.getenv(environment)
            ?: System.getProperty(property)?.takeIf { it.isNotBlank() }

    fun positiveInt(option: String, environment: String, property: String, default: Int): Int? {
        val raw = configuredValue(option, environment, property) ?: return default
        val value = raw.toIntOrNull()
        if (value == null || value <= 0) {
            System.err.println("$option/$environment/$property must be a positive integer (got '$raw')")
            return null
        }
        return value
    }

    fun samplingTemperature(option: String, environment: String, property: String, default: Double): Double? {
        val raw = configuredValue(option, environment, property) ?: return default
        val value = raw.toDoubleOrNull()
        if (value == null || value < 0.0 || value > 2.0) {
            System.err.println("$option/$environment/$property must be in [0, 2] (got '$raw')")
            return null
        }
        return value
    }

    val legacyLocalSelection = cmdLine.hasOption("local-model") || cmdLine.hasOption("local-model-path")
    val explicitBackendValue = cmdLine.getOptionValue("llm")
    val configuredBackendValue = System.getenv("AREND_LLM_BACKEND")
        ?: System.getProperty("llm.backend")?.takeIf { it.isNotBlank() }
    val backend = if (explicitBackendValue != null) {
        LLMBackend.parse(explicitBackendValue) ?: run {
            System.err.println("--llm must be 'local' or 'remote' (got '$explicitBackendValue')")
            return
        }
    } else if (legacyLocalSelection) {
        LLMBackend.LOCAL
    } else if (configuredBackendValue != null) {
        LLMBackend.parse(configuredBackendValue) ?: run {
            System.err.println("AREND_LLM_BACKEND/llm.backend must be 'local' or 'remote' (got '$configuredBackendValue')")
            return
        }
    } else {
        LLMBackend.REMOTE
    }
    if (legacyLocalSelection && explicitBackendValue != null && backend == LLMBackend.REMOTE) {
        System.err.println("--local-model/--local-model-path conflicts with --llm remote")
        return
    }

    val regimeValue = configuredValue("regime", "AREND_LLM_REGIME", "llm.regime")
    val promptFormat = if (regimeValue != null) {
        parsePromptRegime(regimeValue) ?: run {
            System.err.println(
                "--regime must be 'qwen3-direct-v1', 'fine-tuned', or 'instruction' (got '$regimeValue')"
            )
            return
        }
    } else {
        defaultPromptRegime(backend)
    }

    val candidateModeValue = configuredValue(
        "candidate-mode",
        "AREND_LLM_CANDIDATE_MODE",
        "llm.candidate.mode"
    )
    val candidateGenerationMode = if (candidateModeValue != null) {
        parseCandidateMode(candidateModeValue) ?: run {
            System.err.println("--candidate-mode must be 'iterative' or 'batch' (got '$candidateModeValue')")
            return
        }
    } else {
        defaultCandidateMode(promptFormat)
    }
    if (
        promptFormat == TacticPromptFormat.QWEN3_DIRECT_V1 &&
        candidateGenerationMode != CandidateGenerationMode.BATCH
    ) {
        System.err.println("qwen3-direct-v1 requires --candidate-mode batch; direct-v1 has no recovery training")
        return
    }

    val localContextSize = positiveInt(
        "local-context-size",
        "LOCAL_AREND_CONTEXT_SIZE",
        "local.context.size",
        LocalLlamaLLMClient.DEFAULT_CONTEXT_SIZE
    ) ?: return
    val localMaxTokens = positiveInt(
        "local-max-tokens",
        "LOCAL_AREND_MAX_TOKENS",
        "local.max.tokens",
        LocalLlamaLLMClient.DEFAULT_MAX_TOKENS
    ) ?: return
    val localStartupTimeoutSeconds = positiveInt(
        "local-startup-timeout-seconds",
        "LOCAL_AREND_STARTUP_TIMEOUT_SECONDS",
        "local.startup.timeout.seconds",
        LocalLlamaLLMClient.DEFAULT_STARTUP_TIMEOUT_SECONDS.toInt()
    )?.toLong() ?: return
    val maxAttempts = positiveInt(
        "max-attempts",
        "AREND_LLM_MAX_ATTEMPTS",
        "llm.max.attempts",
        CliLLMStepGenerator.DEFAULT_MAX_ATTEMPTS
    ) ?: return
    val maxCandidates = positiveInt(
        "max-candidates",
        "AREND_LLM_MAX_CANDIDATES",
        "llm.max.candidates",
        CliLLMStepGenerator.DEFAULT_MAX_CANDIDATES
    ) ?: return
    val batchTemperature = samplingTemperature(
        "batch-temperature",
        "AREND_LLM_BATCH_TEMPERATURE",
        "llm.batch.temperature",
        CliLLMStepGenerator.DEFAULT_BATCH_TEMPERATURE
    ) ?: return
    val localModelPath: Path = cmdLine.getOptionValue("local-model-path")
        ?.let(Paths::get)
        ?: System.getenv("LOCAL_AREND_MODEL_PATH")?.let(Paths::get)
        ?: System.getProperty("local.model.path")?.takeIf { it.isNotBlank() }?.let(Paths::get)
        ?: LocalLlamaLLMClient.defaultModelPath()
    val llamaServerExecutable = configuredValue(
        "llama-server",
        "LLAMA_SERVER",
        "local.llama.server.executable"
    ) ?: "llama-server"
    val premisesPath = configuredValue("premises-file", "AREND_LLM_PREMISES_FILE", "llm.premises.file")
        ?.let(Paths::get)
    val premises = try {
        premisesPath?.let(::loadPremises) ?: emptyList()
    } catch (e: Exception) {
        System.err.println("Could not load premises: ${e.message}")
        return
    }
    if (promptFormat == TacticPromptFormat.QWEN3_DIRECT_V1 && premisesPath == null) {
        System.err.println(
            "Warning: qwen3-direct-v1 is running with an empty <PREMISES> section; " +
                    "provide --premises-file, AREND_LLM_PREMISES_FILE, or llmPremisesFile " +
                    "for theorem-specific declarations."
        )
    }

    println("Connecting to Arend CLI for library at $libPath...")
    CliConnection(Paths.get(libPath)).use { cli ->
        println("Connected. Finding goals in $moduleDef...")
        val initialProof = PlainTextProof.initial(cli, moduleDef)
        val goals = initialProof.goals()

        if (goals.isEmpty()) {
            println("No goals found in $moduleDef")
            return
        }

        println("Found ${goals.size} goal(s):")
        for (goal in goals) {
            println("  $goal")
        }

        val llmClient: LLMClient = try {
            if (backend == LLMBackend.LOCAL) {
                println("Loading local tactic model from ${localModelPath.toAbsolutePath().normalize()}...")
                LocalLlamaLLMClient.start(
                    modelPath = localModelPath,
                    contextSize = localContextSize,
                    maxTokens = localMaxTokens,
                    parallel = if (candidateGenerationMode == CandidateGenerationMode.BATCH) {
                        CliLLMStepGenerator.batchCompletionCount(
                            promptFormat,
                            maxAttempts,
                            maxCandidates
                        )
                    } else {
                        LocalLlamaLLMClient.DEFAULT_PARALLEL
                    },
                    startupTimeoutSeconds = localStartupTimeoutSeconds,
                    executable = llamaServerExecutable
                ).also { println("Local model ready at ${it.baseUrl}") }
            } else {
                OpenAILikeLLMClient(
                    apiKey = openaiLikeApiKey,
                    model = cmdLine.getOptionValue("model", openaiLikeModel),
                    baseUrl = openaiLikeBaseUrl,
                    maxTokens = openaiLikeMaxTokens,
                    enableThinking = openaiLikeEnableThinking
                )
            }
        } catch (e: Exception) {
            System.err.println("Could not initialize LLM: ${e.message}")
            return
        }

        (llmClient as AutoCloseable).use {
            val backendName = backend.name.lowercase()
            val regimeName = promptRegimeName(promptFormat)
            val candidateModeName = when (candidateGenerationMode) {
                CandidateGenerationMode.ITERATIVE_FEEDBACK -> "iterative"
                CandidateGenerationMode.BATCH -> "batch"
            }
            println("LLM configuration: backend=$backendName, regime=$regimeName, candidate-mode=$candidateModeName")
            val generator = CliLLMStepGenerator(
                cli,
                moduleDef,
                premises = premises,
                maxAttempts = maxAttempts,
                maxCandidates = maxCandidates,
                candidateGenerationMode = candidateGenerationMode,
                promptFormat = promptFormat,
                batchTemperature = batchTemperature,
                llmClient = llmClient
            )
            val search = BestFirstSearch<PlainTextGoal>(generator)

            println("Starting proof search...")
            val result = try {
                search.search(initialProof)
            } catch (e: typechecker.LLMUnavailableException) {
                println("\nProof search aborted: ${e.message}")
                return
            }

            if (result != null) {
                println("\nFound proof!")
                println(result)
            } else {
                println("\nProof search exhausted without finding a proof.")
            }
        }
    }
}
