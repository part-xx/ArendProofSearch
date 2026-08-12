package typechecker.cli.proofstep

// LLM dependencies - commented out for build
// Uncomment later to use JetBrains/koog or other LLM backend
//import ai.koog.agents.core.agent.AIAgent
//import ai.koog.prompt.llm.LLModel
import kotlinx.coroutines.runBlocking
//import org.example.org.jetbrains.ai.kotlin.playbook.createLiteLLMModel
//import org.example.org.jetbrains.ai.kotlin.playbook.createLiteLLMPromptExecutor
//import org.jetbrains.ai.kotlin.playbook.LITELLM_API_KEY
//import org.jetbrains.ai.kotlin.playbook.LITELLM_URL
//import org.jetbrains.ai.kotlin.playbook.LLM_MODEL_ID
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.cli.*
import typechecker.LLMClient
import typechecker.LLMUnavailableException
import typechecker.OpenAILikeLLMClient

import java.io.File

// Gradle properties - read from gradle.properties file
val openaiLikeApiKey: String = System.getenv("OPENAI_LIKE_API_KEY") ?: loadProperty("openaiLikeApiKey") ?: ""
val openaiLikeBaseUrl: String = System.getenv("OPENAI_LIKE_BASE_URL") ?: loadProperty("openaiLikeBaseUrl") ?: ""
val openaiLikeModel: String = System.getenv("OPENAI_LIKE_MODEL") ?: loadProperty("openaiLikeModel") ?: ""
val openaiLikeMaxTokens: Int = (System.getenv("OPENAI_LIKE_MAX_TOKENS") ?: loadProperty("openaiLikeMaxTokens"))?.toIntOrNull() ?: 1024
val openaiLikeEnableThinking: Boolean = (System.getenv("OPENAI_LIKE_ENABLE_THINKING") ?: loadProperty("openaiLikeEnableThinking"))?.toBoolean() ?: false

private fun loadProperty(name: String): String? {
    val gradleProps = File("gradle.properties")
    if (gradleProps.exists()) {
        val props = java.util.Properties().apply {
            load(gradleProps.inputStream())
        }
        return props.getProperty(name)
    }
    return null
}

class CliLLMStepGenerator(
    private val cli: CliApi,
    private val moduleDef: String,
    private val premises: List<String> = emptyList(),
    private val maxAttempts: Int = 10,
    /** How many distinct validated step candidates to collect per goal. */
    private val maxCandidates: Int = 2,
    /**
     * true  — history-based: the model sees previous failures/successes and is told
     *         to provide a NEW, different attempt after each accepted candidate.
     * false — independent attempts: every attempt runs with the same fresh prompt
     *         (no error history, no knowledge of previous successes). Duplicates
     *         are filtered mechanically; diversity comes from temperature sampling.
     */
    private val seekAlternatives: Boolean = false,
    private val llmClient: LLMClient = OpenAILikeLLMClient(
        apiKey = openaiLikeApiKey,
        model = openaiLikeModel,
        baseUrl = openaiLikeBaseUrl,
        maxTokens = openaiLikeMaxTokens,
        enableThinking = openaiLikeEnableThinking
    )
) : ProofStepGenerator<PlainTextGoal> {

    // LLM dependencies - commented out for build
    // Uncomment later to use JetBrains/koog or other LLM backend
    //private val executor = createLiteLLMPromptExecutor(LITELLM_URL, LITELLM_API_KEY)
    //private val llmModel: LLModel = createLiteLLMModel(liteLLMModelId)

    private val sigInfoCache = mutableMapOf<String, SignatureInfoResponse>()

    /** A \class / \record premise: the fields it declares and the classes it extends. */
    private data class ClassPremise(val name: String, val parents: List<String>, val fields: List<String>)

    /** field name -> its declared text, used when the CLI has no signature for it. */
    private val fieldDeclarations = mutableMapOf<String, String>()
    private val classPremises: List<ClassPremise> =
        premises.filter { isClassOrRecord(it) }.map { parseClassPremise(it) }
    /**
     * Classes themselves are never shown to the model — only their fields are, each
     * annotated with the classes it can be accessed on (the declaring one plus every
     * premise class transitively extending it).
     */
    private val fieldOwners: Map<String, List<String>> = computeFieldOwners()
    /**
     * Validated step terms per semantic goal ([PlainTextGoal] equality ignores the
     * positional id). Unlike ProofSteps, terms are goal-relative, so they can be
     * reused when the same goal arises in a DIFFERENT proof state: re-applying a
     * term to the new state only needs a typechecker check, not another LLM round.
     */
    private val stepTermCache = mutableMapOf<PlainTextGoal, List<String>>()
    private val systemPrompt = buildSystemPrompt()
    private val preprompt: String
    private val lemmaSignature: String = cli.signature(moduleDef)

    init {
        val modulePrefix = moduleDef.substringBefore(":")
        val moduleDefinitions = buildModuleDefinitions(modulePrefix)

        fetchPremiseSignatures()

        val premisesBlock = if (premises.isNotEmpty())
            "Available functions (use [APPLY name] to apply):\n${formatPremises()}\n" +
                    "Entries marked [field of A, B] are record/class fields: apply them on an instance " +
                    "of one of those classes with dot notation, e.g. [APPLY inst.field].\n"
        else ""

        println("Premises: ")
        println(premisesBlock)

        preprompt = "Definitions in current module:\n$moduleDefinitions\n" +
                premisesBlock +
                "--- ACTUAL GOAL TO SOLVE ---\n"
    }

    private fun fetchPremiseSignatures() {
        for (premise in premises) {
            val name = extractPremiseName(premise) ?: continue
            cacheSignature(name)

            if (isDataPremise(premise)) {
                for (constructor in extractBarNames(premise)) cacheSignature(constructor)
            }
        }
        for (field in fieldOwners.keys) cacheSignature(field)
    }

    private fun cacheSignature(name: String) {
        if (name in sigInfoCache) return
        val info = cli.signatureInfo(moduleDef, name)
        if (info != null) sigInfoCache[name] = info
    }

    private fun extractPremiseName(premise: String): String? {
        val match = Regex("""(?:\\truncated\s+)?\\(?:func|lemma|meta|data|class|record)\s+(?:\\[a-z]+\s+\d+\s+)?(\S+)""").find(premise)
        return match?.groupValues?.get(1)
    }

    private fun isClassOrRecord(premise: String): Boolean {
        val trimmed = premise.trimStart()
        return trimmed.startsWith("\\class") || trimmed.startsWith("\\record")
    }

    private fun isDataPremise(premise: String): Boolean {
        val trimmed = premise.trimStart()
        return trimmed.startsWith("\\data") || trimmed.startsWith("\\truncated")
    }

    /** Names introduced by `| name ...` clauses (data constructors, class fields). */
    private fun extractBarNames(premise: String): List<String> {
        return Regex("""^\s*\|\s+(\S+)""", RegexOption.MULTILINE)
            .findAll(premise)
            .map { it.groupValues[1] }
            .toList()
    }

    /**
     * Splits a class/record premise into its name, its `\extends` parents and the
     * fields it declares itself — both the parenthesized header parameters
     * (`(\coerce val : M) (elem inv : M)`) and the `| field : type` clauses.
     * Field IMPLEMENTATIONS (`| elem => ide`) declare nothing new and are skipped.
     */
    private fun parseClassPremise(premise: String): ClassPremise {
        val name = extractPremiseName(premise) ?: ""
        val header = premise.substringBefore("|")

        val parents = Regex("""\\extends\s+([^|\n]+)""").find(header)
            ?.groupValues?.get(1)
            ?.split(",")
            ?.map { it.trim() }
            ?.filter { it.isNotEmpty() }
            ?: emptyList()

        val fields = mutableListOf<String>()
        for (group in topLevelParenGroups(header.substringBefore("\\extends"))) {
            val colonIdx = group.indexOf(':')
            if (colonIdx < 0) continue
            val declared = group.substring(0, colonIdx).trim().split("\\s+".toRegex())
                .filter { it.isNotEmpty() && !it.startsWith("\\") }
            for (field in declared) {
                fields.add(field)
                fieldDeclarations.putIfAbsent(field, "$field : ${group.substring(colonIdx + 1).trim()}")
            }
        }
        for (line in premise.lines()) {
            val match = Regex("""^\s*\|\s+(\S+)\s*(.*)$""").find(line) ?: continue
            val body = match.groupValues[2]
            if (body.contains("=>")) continue
            val field = match.groupValues[1]
            fields.add(field)
            fieldDeclarations.putIfAbsent(field, "$field $body".trim())
        }
        return ClassPremise(name, parents, fields.distinct())
    }

    /** Contents of the top-level `(...)` groups of [s], in order (implicit `{...}` ones are not fields to apply). */
    private fun topLevelParenGroups(s: String): List<String> {
        val groups = mutableListOf<String>()
        var i = 0
        while (i < s.length) {
            if (s[i] == '(') {
                val close = findMatchingParen(s, i)
                if (close < 0) break
                groups.add(s.substring(i + 1, close))
                i = close + 1
            } else i++
        }
        return groups
    }

    /**
     * Maps every field declared by a class/record premise to the classes it is
     * available on: the declaring class first, then each premise class that extends
     * it (transitively), in premise order.
     */
    private fun computeFieldOwners(): Map<String, List<String>> {
        val byName = classPremises.associateBy { it.name }

        fun ancestorsOf(cls: ClassPremise): List<String> {
            val seen = linkedSetOf<String>()
            fun visit(cur: ClassPremise) {
                for (parent in cur.parents) {
                    if (seen.add(parent)) byName[parent]?.let { visit(it) }
                }
            }
            visit(cls)
            return seen.toList()
        }

        val owners = linkedMapOf<String, MutableList<String>>()
        for (cls in classPremises) {
            for (field in cls.fields) owners.getOrPut(field) { mutableListOf() }.add(cls.name)
            for (ancestor in ancestorsOf(cls)) {
                val inherited = byName[ancestor]?.fields ?: continue
                for (field in inherited) owners.getOrPut(field) { mutableListOf() }.add(cls.name)
            }
        }
        return owners.mapValues { (_, names) -> names.distinct() }
    }

    private fun formatPremises(): String {
        val lines = premises
            .filter { !isClassOrRecord(it) }
            .map { premise ->
                val name = extractPremiseName(premise)
                val info = name?.let { sigInfoCache[it] }
                if (info != null && info.resultType != null) {
                    formatPremiseWithInfo(name, info)
                } else {
                    "  $premise"
                }
            }
            .toMutableList()
        lines.addAll(formatClassFields())
        return lines.joinToString("\n")
    }

    /** Class/record premises are shown as their fields only, each tagged with its owning classes. */
    private fun formatClassFields(): List<String> {
        return fieldOwners.map { (field, owners) ->
            val info = sigInfoCache[field]
            val body = if (info != null && info.resultType != null) {
                formatPremiseWithInfo(field, info)
            } else {
                "  ${fieldDeclarations[field] ?: field}"
            }
            "$body  [field of ${owners.joinToString(", ")}]"
        }
    }

    private fun formatPremiseWithInfo(name: String, info: SignatureInfoResponse): String {
        val explicitParams = info.params.filter { it.explicit }

        // Implicit params in declaration order — the model pins them positionally
        // with {braces} (e.g. path endpoints of *>, which are uninferrable otherwise).
        val implicitArgs = info.params
            .filter { !it.explicit }
            .joinToString(" ") { "{${it.name}: ${it.type}}" }
        val provideArgs = explicitParams
            .filter { !it.propositional }
            .joinToString(", ") { "${it.name}: ${it.type}" }
        val subgoalArgs = explicitParams
            .filter { it.propositional }
            .joinToString(", ") { "${it.name}: ${it.type}" }
        val resultStr = info.resultType ?: "?"

        val parts = mutableListOf<String>()
        if (implicitArgs.isNotEmpty()) parts.add("implicits: $implicitArgs")
        if (provideArgs.isNotEmpty()) parts.add("provide: $provideArgs")
        if (subgoalArgs.isNotEmpty()) parts.add("subgoals: $subgoalArgs")

        val annotation = if (parts.isNotEmpty()) "  [${parts.joinToString("; ")}]" else ""
        return "  $name($provideArgs) : $resultStr$annotation"
    }

    private fun buildModuleDefinitions(modulePrefix: String): String {
        val scope = try { cli.getScope(moduleDef, "0") } catch (_: Exception) { return "" }
        val defName = moduleDef.substringAfter(":")
        val moduleName = modulePrefix
        val defsToFetch = scope.scope
            .filter { it.kind in setOf("DATA", "FUNCTION") }
            .filter { it.module == moduleName }
            .filter { it.name != defName }
            .map { it.name }

        val sigs = mutableListOf<String>()
        for (name in defsToFetch) {
            try {
                val sig = cli.signature("$modulePrefix:$name")
                if (sig.isNotBlank()) sigs.add(sig)
            } catch (_: Exception) {}
        }
        return sigs.joinToString("\n")
    }

    fun buildTermFromApply(name: String, providedArgs: List<String>): String? {
        val info = if (name.contains('.')) {
            sigInfoCache[name.substringAfterLast('.')]
        } else {
            sigInfoCache[name]
        } ?: return null

        val explicitParams = info.params.filter { it.explicit }

        val implicitParamCount = info.params.count { !it.explicit }
        // Ignore extra brace args beyond the declared implicits.
        val implicitArgs = providedArgs.filter { it.startsWith("{") && it.endsWith("}") }
            .take(implicitParamCount)
        val explicitProvided = providedArgs.filter { !(it.startsWith("{") && it.endsWith("}")) }

        val parts = mutableListOf(name)
        parts.addAll(implicitArgs)

        var argIdx = 0
        for (param in explicitParams) {
            // Propositional args are NEVER taken from the model — always filled as
            // {?} subgoals; a value the model provides for them is ignored.
            if (!param.propositional && argIdx < explicitProvided.size) {
                val v = explicitProvided[argIdx++]
                if (v.contains(' ') || v.startsWith("\\")) {
                    parts.add("($v)")
                } else {
                    parts.add(v)
                }
            } else {
                parts.add("{?}")
            }
        }
        return parts.joinToString(" ")
    }

    fun buildCaseExpression(splitExpr: String, datatype: String, dataModule: String, isVariable: Boolean = false, topLevel: Boolean = false): String? {
        val info = cli.signatureInfo(dataModule, datatype)
        val constructors = info?.constructors
        if (constructors.isNullOrEmpty()) return null

        var nameIdx = 0
        val clauses = constructors.joinToString(" | ") { con ->
            val explicitParams = con.params.filter { it.explicit }
            val pattern = if (explicitParams.isEmpty()) {
                con.name
            } else {
                val paramNames = explicitParams.map { p ->
                    if (p.name == "_") {
                        val c = ('a' + nameIdx % 26)
                        nameIdx++
                        c.toString()
                    } else {
                        p.name
                    }
                }
                "${con.name} ${paramNames.joinToString(" ")}"
            }
            "$pattern => {?}"
        }

        if (topLevel && isVariable) {
            return "\\elim $splitExpr | $clauses"
        }
        val caseHead = if (isVariable) "\\case \\elim $splitExpr" else "\\case $splitExpr"
        return "$caseHead \\with { | $clauses }"
    }

    fun buildIntroExpression(providedNames: List<String>, goal: PlainTextGoal): String {
        if (providedNames.isNotEmpty()) {
            return "\\lam ${providedNames.joinToString(" ")} => {?}"
        }
        val names = extractPiBinderNames(goal.expectedType)
        return if (names.isNotEmpty()) {
            "\\lam ${names.joinToString(" ")} => {?}"
        } else {
            "\\lam _ => {?}"
        }
    }

    private fun extractPiBinderNames(type: String): List<String> {
        val names = mutableListOf<String>()
        var rest = type.trim()
        while (true) {
            if (rest.startsWith("\\Pi")) {
                rest = rest.removePrefix("\\Pi").trimStart()
                while (rest.startsWith("(")) {
                    val closeParen = findMatchingParen(rest, 0)
                    if (closeParen < 0) return names
                    val inside = rest.substring(1, closeParen).trim()
                    val colonIdx = inside.indexOf(':')
                    if (colonIdx > 0) {
                        val paramNames = inside.substring(0, colonIdx).trim().split("\\s+".toRegex())
                        names.addAll(paramNames.filter { it.isNotEmpty() })
                    }
                    rest = rest.substring(closeParen + 1).trimStart()
                }
                if (rest.startsWith("->")) {
                    rest = rest.removePrefix("->").trimStart()
                }
            } else if (rest.contains("->")) {
                names.add("_")
                rest = rest.substringAfter("->").trimStart()
            } else {
                break
            }
        }
        return names
    }

    fun extractTypeName(typeStr: String): String {
        val firstWord = typeStr.split("\\s+".toRegex()).first()
        val prefixInfo = cli.signatureInfo(moduleDef, firstWord)
        if (prefixInfo?.constructors != null) return firstWord

        for (token in typeStr.split("\\s+".toRegex())) {
            if (token.isNotEmpty() && !token[0].isLetterOrDigit() && token[0] !in "{(\\_") {
                val info = cli.signatureInfo(moduleDef, token)
                if (info?.constructors != null) return token
            }
        }
        return firstWord
    }

    private fun findMatchingParen(s: String, openIdx: Int): Int {
        var depth = 0
        for (i in openIdx until s.length) {
            when (s[i]) {
                '(' -> depth++
                ')' -> { depth--; if (depth == 0) return i }
            }
        }
        return -1
    }

    data class ParsedStep(val type: String, val name: String?, val args: List<String>, val rawTerm: String?)

    fun parseStepFromResponse(response: String): ParsedStep? {
        data class Candidate(val position: Int, val step: ParsedStep)

        val candidates = mutableListOf<Candidate>()

        val applyPattern = Regex("""\[APPLY\s+(\S+)\](.*?)\[/APPLY\]""", RegexOption.DOT_MATCHES_ALL)
        for (m in applyPattern.findAll(response)) {
            val name = m.groupValues[1]
            val body = m.groupValues[2].trim()
            val args = body.lines().map { it.trim() }.filter { it.isNotEmpty() }
            candidates.add(Candidate(m.range.first, ParsedStep("apply", name, args, null)))
        }

        val rewritePattern = Regex("""\[REWRITE\](.*?)\[/REWRITE\]""", RegexOption.DOT_MATCHES_ALL)
        for (m in rewritePattern.findAll(response)) {
            val equality = m.groupValues[1].trim()
            if (equality.isNotEmpty()) {
                candidates.add(Candidate(m.range.first, ParsedStep("rewrite", null, emptyList(), equality)))
            }
        }

        val refinePattern = Regex("""\[REFINE\](.*?)\[/REFINE\]""", RegexOption.DOT_MATCHES_ALL)
        for (m in refinePattern.findAll(response)) {
            val term = m.groupValues[1].trim()
            if (term.isNotEmpty()) {
                candidates.add(Candidate(m.range.first, ParsedStep("refine", null, emptyList(), term)))
            }
        }

        val casePattern = Regex("""\[CASE\](.*?)\[/CASE\]""", RegexOption.DOT_MATCHES_ALL)
        for (m in casePattern.findAll(response)) {
            val caseExpr = m.groupValues[1].trim()
            if (caseExpr.isNotEmpty()) {
                candidates.add(Candidate(m.range.first, ParsedStep("case", null, emptyList(), caseExpr)))
            }
        }

        val introPattern = Regex("""\[INTRO\](.*?)\[/INTRO\]""", RegexOption.DOT_MATCHES_ALL)
        for (m in introPattern.findAll(response)) {
            val body = m.groupValues[1].trim()
            val names = if (body.isNotEmpty()) body.split("\\s+".toRegex()) else emptyList()
            candidates.add(Candidate(m.range.first, ParsedStep("intro", null, names, null)))
        }

        return candidates.maxByOrNull { it.position }?.step
    }

    /** Invalidates the memoized negative result for a goal the search wants to retry. */
    override fun onRetryGoal(goal: PlainTextGoal) {
        stepTermCache.remove(goal)
    }

    override fun generate(goal: PlainTextGoal, currentProof: Proof<PlainTextGoal>?): List<ProofStep<PlainTextGoal>> {
        val currentProofText = (currentProof as? PlainTextProof)?.proofText ?: "{?}"

        // Reuse steps already proven for this goal in another proof state:
        // re-validate each memoized term against the CURRENT state (typechecker
        // call only, no LLM round). Falls through to LLM generation if nothing
        // memoized validates here.
        val memoizedTerms = stepTermCache[goal]
        if (memoizedTerms != null) {
            if (memoizedTerms.isEmpty()) {
                println("No candidates were found for this goal in a previous state (memoized) — not retrying")
                return emptyList()
            }
            println("Reusing ${memoizedTerms.size} memoized step(s) for this goal in a new proof state")
            val reused = memoizedTerms.mapNotNull { term ->
                when (val validation = validateTerm(term, goal, currentProofText)) {
                    is Validation.Success -> validation.step
                    else -> {
                        println("Memoized step '$term' does not validate in the new state, discarding it")
                        null
                    }
                }
            }
            if (reused.isNotEmpty()) return reused
        }

        val context = goal.contextBindings.joinToString("\n") { "${it.name} : ${it.type}" }

        val initialPrompt = preprompt +
                "Signature: $lemmaSignature\n" +
                "Context: $context\n" +
                "Expected type: ${goal.expectedType}\n" +
                "Current proof: $currentProofText\n" +
                "\nProvide CORRECT COMPLETION EXPRESSION."
        var currentPromptPadding = "\n"

        println("Expected type: ${goal.expectedType}")
        println("Context: $context")

        // if (!seekAlternatives) {
        //    return generateIndependent(goal, currentProofText, currentPrompt)
       // }

        val failedAttempts = mutableSetOf<String>()
        val attemptErrors = mutableMapOf<String, String>()
        val attemptHistory = mutableListOf<Pair<String, String>>()
        val candidates = mutableListOf<ProofStep<PlainTextGoal>>()
        val acceptedTerms = mutableSetOf<String>()
        val acceptedTermList = mutableListOf<String>()
        var temperature = 0.7
        var consecutiveDuplicates = 0

        for (attempt in 0 until maxAttempts) {
            if (candidates.size >= maxCandidates) break
            println("Attempt ${attempt + 1} (temperature=$temperature)")
            // LLM dependencies - commented out for build
            // Uncomment later to use JetBrains/koog or other LLM backend
            //val agent = AIAgent(
            //    executor = executor,
            //    systemPrompt = systemPrompt,
            //    llmModel = llmModel,
            //    temperature = temperature,
            //)
            //val response = runBlocking { agent.run(currentPrompt) }
            val response = try {
                runBlocking { llmClient.generateResponse(systemPrompt, initialPrompt + currentPromptPadding, temperature) }
            } catch (e: Exception) {
                // Infra failure (unreachable endpoint, auth, ...). Retrying proof
                // attempts is pointless and slow (~1 min of client backoff each) —
                // abort the search with a clear diagnosis instead of a raw stack trace.
                throw LLMUnavailableException(
                    "LLM API call failed after client retries — check network/VPN/endpoint " +
                    "(${e.message})"
                )
            }
            println("The response:\n${response.chunked(120).joinToString("\n")}")

            if (response in failedAttempts) {
                consecutiveDuplicates++
                temperature = minOf(temperature + 0.1, 1.0)
                println("DUPLICATE — exact same response (x$consecutiveDuplicates), raising temperature to $temperature")
                currentPromptPadding += "\n\nYou produced the EXACT SAME response again — it was already rejected. " +
                        rejectedSummary(attemptErrors) +
                        duplicateEscalation(consecutiveDuplicates) +
                        "Provide a GENUINELY NEW attempt — do not rephrase a rejected approach."
                continue
            }

            val step = parseStepFromResponse(response)
            if (step == null) {
                println("Could not extract step from response")
                currentPromptPadding += "\n\nYour previous response did not contain a valid step. " +
                        "Use [APPLY name]...[/APPLY], [REWRITE]...[/REWRITE], [CASE]...[/CASE], [INTRO]...[/INTRO], " +
                        "or [REFINE]...[/REFINE]. " +
                        "Do NOT use ```arend code blocks."
                continue
            }

            val term = when (val construction = buildTermFromStep(step, goal, currentProofText)) {
                is StepConstruction.Fatal -> {
                    println(construction.message)
                    return emptyList()
                }
                is StepConstruction.Failure -> {
                    failedAttempts.add(response)
                    currentPromptPadding += construction.feedback
                    continue
                }
                is StepConstruction.Term -> construction.value
            }
            println("Final term: $term")

            // pmap with an identity function is a definitional NO-OP: it re-creates
            // the same goal (reported as an unreduced beta-form the string-based
            // no-progress guards cannot recognize) and loops forever. Reject early.
            if (IDENTITY_PMAP.containsMatchIn(term)) {
                println("Rejecting no-op step: pmap with an identity function changes nothing")
                failedAttempts.add(response)
                currentPromptPadding += "\n\nYour step uses pmap with an identity function (pmap (\\lam x => x)) — " +
                        "a definitional NO-OP that just re-creates the same goal. " +
                        "Use the equality directly, or pmap a function that actually transforms the sides.\n"
                continue
            }

            val normalizedTerm = term.replace("\\s+".toRegex(), " ").trim()
            if (normalizedTerm in failedAttempts) {
                consecutiveDuplicates++
                temperature = minOf(temperature + 0.1, 1.0)
                println("DUPLICATE — term '$normalizedTerm' already rejected (x$consecutiveDuplicates), raising temperature to $temperature")
                val prevError = attemptErrors[normalizedTerm]
                currentPromptPadding += "\n\nYou already proposed '$term' — it was rejected" +
                        (if (prevError != null) " with this error:\n$prevError\n" else ".\n") +
                        rejectedSummary(attemptErrors) +
                        duplicateEscalation(consecutiveDuplicates) +
                        "Do NOT propose it again. Provide a genuinely different step."
                continue
            }
            if (normalizedTerm in acceptedTerms) {
                if (seekAlternatives) {
                    consecutiveDuplicates++
                    temperature = minOf(temperature + 0.1, 1.0)
                    println("DUPLICATE — term '$normalizedTerm' already ACCEPTED (x$consecutiveDuplicates), raising temperature to $temperature")
                    currentPromptPadding += "\n\nYou already proposed '$term' — it was ACCEPTED as a candidate. " +
                            duplicateEscalation(consecutiveDuplicates) +
                            "Provide a DIFFERENT step, not an accepted one."
                } else {
                    temperature = minOf(temperature + 0.1, 1.0)
                    println("DUPLICATE — term '$normalizedTerm' already ACCEPTED, raising temperature to $temperature")
                }
                continue
            }

            when (val validation = validateTerm(term, goal, currentProofText)) {
                is Validation.Success -> {
                    // No-progress guard: a step whose ONLY subgoal is identical (same
                    // type and context) to the current goal sends the search into a
                    // regress loop (e.g. pmap (\lam x => x) on an equality goal).
                    val newGoals = validation.step.proof.goals()
                    if (newGoals.size == 1 && newGoals[0] == goal) {
                        println("Step leaves an identical subgoal — no progress, rejecting")
                        failedAttempts.add(normalizedTerm)
                        attemptErrors[normalizedTerm] = "Step leaves a subgoal identical to the goal (no progress)"
                        currentPromptPadding += "\n\nWRONG guess (#${failedAttempts.size}): $term\n" +
                                "It typechecks but its only subgoal is IDENTICAL to the current goal — no progress. " +
                                "Provide a step that actually reduces the goal.\n"
                        continue
                    }
                    // Dead-subgoal pruning: leading into a goal the LLM already
                    // exhausted in a previous state (memoized as empty) makes this
                    // step a known dead end.
                    if (newGoals.any { stepTermCache[it]?.isEmpty() == true }) {
                        println("Step leads into an already-exhausted goal — rejecting")
                        failedAttempts.add(normalizedTerm)
                        attemptErrors[normalizedTerm] = "Step leads into an already-exhausted goal (dead end)"
                        currentPromptPadding += "\n\nWRONG guess (#${failedAttempts.size}): $term\n" +
                                "It typechecks but leads into a subgoal that was already tried and exhausted with no candidates — a known dead end. " +
                                "Provide a step that avoids it.\n"
                        continue
                    }
                    candidates.add(validation.step)
                    acceptedTerms.add(normalizedTerm)
                    acceptedTermList.add(normalizedTerm)
                    consecutiveDuplicates = 0
                    println("Candidate #${candidates.size} accepted: $term")
                    if (seekAlternatives) {
                        currentPromptPadding += "\n\nACCEPTED as candidate #${candidates.size}: $term\n" +
                                "This step is correct and recorded. Now provide a DIFFERENT step for the SAME goal " +
                                "(a different lemma, tactic, or strategy). Do NOT repeat accepted or rejected approaches."
                    } else {
                        currentPromptPadding = "\n"
                    }
                    continue
                }
                is Validation.Error -> {
                    failedAttempts.add(normalizedTerm)
                    consecutiveDuplicates = 0
                    val errorMsg = validation.errorMsg
                    attemptErrors[normalizedTerm] = errorMsg
                    println("Errors: $errorMsg")

                    val progressNote = buildProgressNote(attemptHistory, errorMsg, term)
                    attemptHistory.add(Pair(term, errorMsg))

                    val inferenceHint = if (ARG_INFERENCE_ERROR.containsMatchIn(errorMsg))
                        "\nHINT: To fix 'Cannot infer parameter X', provide X as an implicit arg wrapped in {braces} in your [APPLY] step, " +
                        "positionally, in the order of the \"implicits:\" list (include ALL implicits before X — you cannot skip earlier ones). " +
                        "Pin the implicit that is NOT already determined by the goal: for goal k = 1 with a : Inv k in context, " +
                        "[APPLY natUnit] {a.inv} [/APPLY] constructs natUnit {a.inv} {?} with subgoal a.inv * k = 1, whereas " +
                        "{k} would create the CIRCULAR subgoal k * k = 1. " +
                        "For *> pin the path endpoints: [APPLY *>] {Nat} {n} {k * k|n.inv} {k} [/APPLY].\n"
                    else ""

                    currentPromptPadding += "\n\n${progressNote}WRONG guess (#${failedAttempts.size}): $term\nErrors:\n$errorMsg\n$inferenceHint\n" +
                            "Provide your corrected attempt."
                    continue
                }
                is Validation.Crashed -> {
                    failedAttempts.add(normalizedTerm)
                    consecutiveDuplicates = 0
                    val errorMsg = validation.errorMsg
                    attemptErrors[normalizedTerm] = errorMsg
                    println("Exception during validation: $errorMsg")

                    val progressNote = buildProgressNote(attemptHistory, errorMsg, term)
                    attemptHistory.add(Pair(term, errorMsg))

                    currentPromptPadding += "\n\n${progressNote}Previous guess: $term\nResulted in error: $errorMsg\n\n" +
                            "Provide your next attempt."
                    continue
                }
            }
        }

        // Memoize the outcome either way: found terms for reuse in other states,
        // or an empty list recording that the LLM exhausted this goal — avoids
        // re-burning maxAttempts on the same goal in every new proof state.
        stepTermCache[goal] = acceptedTermList
        return candidates
    }

    /**
     * Independent-attempts mode ([seekAlternatives] = false): every attempt uses the
     * SAME fresh prompt — the model never sees error history or previous successes.
     * Distinct valid candidates are collected; duplicates are filtered mechanically
     * and diversity comes from the temperature ramp, not from instructions.
     */
    private fun generateIndependent(
        goal: PlainTextGoal,
        currentProofText: String,
        basePrompt: String
    ): List<ProofStep<PlainTextGoal>> {
        val candidates = mutableListOf<ProofStep<PlainTextGoal>>()
        val acceptedTerms = mutableSetOf<String>()
        var temperature = 0.7

        for (attempt in 0 until maxAttempts) {
            if (candidates.size >= maxCandidates) break
            println("Attempt ${attempt + 1} (independent, temperature=$temperature)")
            val response = try {
                runBlocking { llmClient.generateResponse(systemPrompt, basePrompt, temperature) }
            } catch (e: Exception) {
                throw LLMUnavailableException(
                    "LLM API call failed after client retries — check network/VPN/endpoint " +
                    "(${e.message})"
                )
            }
            temperature = minOf(temperature + 0.1, 1.0)
            println("The response:\n${response.chunked(120).joinToString("\n")}")

            val step = parseStepFromResponse(response)
            if (step == null) {
                println("Could not extract step from response")
                continue
            }

            val term = when (val construction = buildTermFromStep(step, goal, currentProofText)) {
                is StepConstruction.Fatal -> {
                    println(construction.message)
                    return candidates
                }
                is StepConstruction.Failure -> {
                    println(construction.feedback)
                    continue
                }
                is StepConstruction.Term -> construction.value
            }
            println("Final term: $term")

            val normalizedTerm = term.replace("\\s+".toRegex(), " ").trim()
            if (normalizedTerm in acceptedTerms) {
                println("Already have this candidate, skipping")
                continue
            }

            when (val validation = validateTerm(term, goal, currentProofText)) {
                is Validation.Success -> {
                    candidates.add(validation.step)
                    acceptedTerms.add(normalizedTerm)
                    println("Candidate #${candidates.size} accepted (independent): $term")
                }
                is Validation.Error -> println("Errors: ${validation.errorMsg}")
                is Validation.Crashed -> println("Exception during validation: ${validation.errorMsg}")
            }
        }
        return candidates
    }

    /** Outcome of turning a parsed step into a candidate term (includes CLI calls for CASE). */
    private sealed interface StepConstruction {
        data class Term(val value: String) : StepConstruction
        /** Recoverable failure; [feedback] is the prompt text the history-based loop feeds back. */
        data class Failure(val feedback: String) : StepConstruction
        /** Unrecoverable CLI failure — give up on the goal. */
        data class Fatal(val message: String) : StepConstruction
    }

    /** Outcome of validating a candidate term via applyStep. */
    private sealed interface Validation {
        data class Success(val step: ProofStep<PlainTextGoal>) : Validation
        /** Typechecker rejected the term. */
        data class Error(val errorMsg: String) : Validation
        /** Validation itself threw (transport/protocol failure). */
        data class Crashed(val errorMsg: String) : Validation
    }

    private fun buildTermFromStep(step: ParsedStep, goal: PlainTextGoal, currentProofText: String): StepConstruction {
        return when (step.type) {
            "apply" -> {
                val name = step.name!!
                val constructed = buildTermFromApply(name, step.args)
                if (constructed != null) {
                    println("Constructed from APPLY: $constructed")
                    StepConstruction.Term(constructed)
                } else {
                    val rawArgs = step.args.joinToString(" ") { v ->
                        if (v.startsWith("{") && v.endsWith("}")) v
                        else if (v.contains(' ') || v.startsWith("\\")) "($v)" else v
                    }
                    val result = "$name $rawArgs".trim()
                    println("Constructed from APPLY (raw): $result")
                    StepConstruction.Term(result)
                }
            }
            "refine" -> {
                val term = step.rawTerm!!
                // A lone hole is not a step: it re-creates the goal unchanged.
                if (term == "{?}") {
                    println("REFINE term is a bare goal — not a step")
                    return StepConstruction.Failure(
                        "\n\nYour [REFINE] term was just {?}, which is not a step — it leaves the goal unchanged. " +
                                "Give the expression that fills the goal, with {?} only for the subproofs it leaves open.\n\n" +
                                "Provide your next attempt."
                    )
                }
                println("Constructed from REFINE: $term")
                StepConstruction.Term(term)
            }
            "rewrite" -> {
                val eq = step.rawTerm!!
                val result = if (eq.contains(' ') || eq.startsWith("\\")) "rewrite ($eq) {?}" else "rewrite $eq {?}"
                println("Constructed from REWRITE: $result")
                StepConstruction.Term(result)
            }
            "case" -> {
                val splitExpr = step.rawTerm!!

                if (splitExpr.contains("{?}")) {
                    println("Split expression $splitExpr should not contain goals {?}")
                    return StepConstruction.Failure(
                        "\n\nSplit expression $splitExpr should not contain goals {?}\n\n" +
                                "Provide your next attempt."
                    )
                }

                // Nested-duplicate guard: the same expression is already case-split in
                // the current proof (an ancestor of this goal). The expected type does
                // not change between a case and its own branches — the context only
                // gains the pattern variable — so re-splitting nests forever without
                // progress. String-level comparison for now (whitespace- and
                // paren-insensitive); TODO: compare split expressions semantically via CLI.
                fun squash(s: String) = s.replace("(", " ").replace(")", " ").replace("\\s+".toRegex(), " ").trim()
                val normalizedProof = squash(currentProofText)
                val normalizedSplit = squash(splitExpr)
                if (normalizedProof.contains("\\case $normalizedSplit \\with") ||
                    normalizedProof.contains("\\case \\elim $normalizedSplit \\with") ||
                    normalizedProof.contains("\\elim $normalizedSplit |")) {
                    println("Nested duplicate CASE on '$splitExpr' — already split in an ancestor of this goal")
                    return StepConstruction.Failure(
                        "\n\n'$splitExpr' is ALREADY case-split in an ancestor of the current goal. " +
                        "The expected type does not change between a case and its own branches (the context only gains the pattern variable), " +
                        "so splitting it again only nests forever without progress. " +
                        "Use the hypotheses bound by the branch pattern instead, or split a DIFFERENT expression.\n\n" +
                        "Provide your next attempt."
                    )
                }

                val binding = goal.contextBindings.find { it.name == splitExpr }

                val cliResponse = cli.typeExpr(moduleDef, goal.id, splitExpr, currentProofText)
                    ?: return StepConstruction.Fatal("CLI invocation error for '$splitExpr'")

                if (cliResponse.error != null) {
                    println("Using case with split expression '$splitExpr' resulted in error: ${cliResponse.error}")
                    return StepConstruction.Failure(
                        "\n\nTypechecking split expression $splitExpr resulted in error: ${cliResponse.error}\n\n" +
                                "Provide your next attempt."
                    )
                }

                val typeName = cliResponse.data?.datatype?.typename
                if (typeName == null) {
                    println("Cannot recognize the type of '$splitExpr' as a datatype")
                    return StepConstruction.Failure(
                        "\n\nCannot recognize the type of '$splitExpr' as a datatype\n\n" +
                                "Provide your next attempt."
                    )
                }
                val dataModule = cliResponse.data.datatype.module
                val isVariable = binding != null
                val isTopLevel = currentProofText.trim() == "{?}"
                val result = buildCaseExpression(splitExpr, typeName, dataModule, topLevel = isTopLevel, isVariable = isVariable)
                println("Constructed from CASE: $result")
                if (result == null) {
                    println("Could not build case expression for '${splitExpr}'")
                    return StepConstruction.Failure(
                        "\n\nCould not build case expression for '${splitExpr}'\n\n" +
                                "Provide your next attempt."
                    )
                }
                StepConstruction.Term(result)
            }
            "intro" -> {
                val result = buildIntroExpression(step.args, goal)
                println("Constructed from INTRO: $result")
                StepConstruction.Term(result)
            }
            else -> {
                println("Unknown step type: ${step.type}")
                StepConstruction.Failure(
                    "\n\nUnknown step type '${step.type}'. Use [APPLY name]...[/APPLY], [REWRITE]...[/REWRITE], " +
                            "[CASE]...[/CASE], [INTRO]...[/INTRO], or [REFINE]...[/REFINE].\n\nProvide your next attempt."
                )
            }
        }
    }

    private fun validateTerm(term: String, goal: PlainTextGoal, currentProofText: String): Validation {
        val goalIndex = goal.id.toIntOrNull() ?: 0
        val wrappedTerm = if (term.contains(' ')) "($term)" else term
        val fullBody = PlainTextProof.replaceNthGoal(currentProofText, goalIndex, wrappedTerm)
            ?: return Validation.Error("Could not find goal ${goal.id} in proof text")

        return try {
            val applyResult = cli.applyStep(moduleDef, fullBody)
            if (applyResult.success) {
                println("applyStep succeeded! Proof: $fullBody")
                val newGoals = applyResult.goals.map { g ->
                    PlainTextGoal(g.id, g.expectedType, g.context, moduleDef)
                }
                // Score = number of new holes: hole pressure steers best-first toward
                // finishing branches (0 new goals) before growing *>/pmap chains.
                Validation.Success(ProofStep(PlainTextProof(cli, moduleDef, fullBody, newGoals), newGoals.size.toDouble()))
            } else {
                Validation.Error(applyResult.errors.joinToString("\n"))
            }
        } catch (e: Exception) {
            Validation.Crashed(e.message ?: "unknown error")
        }
    }

    private fun errorKey(error: String): String {
        return error.lines()
            .filter { it.trimStart().startsWith("Expected type:") || it.trimStart().startsWith("Actual type:") }
            .joinToString("\n") { it.trim() }
    }

    /** Compact list of recently rejected terms with their errors, for duplicate feedback. */
    private fun rejectedSummary(attemptErrors: Map<String, String>): String {
        if (attemptErrors.isEmpty()) return ""
        val items = attemptErrors.entries.toList().takeLast(3).joinToString("\n") { (term, error) ->
            val key = errorKey(error).ifBlank { error.lineSequence().firstOrNull { it.isNotBlank() } ?: "" }
            "- $term  =>  $key"
        }
        return "Rejected approaches so far:\n$items\n"
    }

    /** Escalating warning once the model keeps repeating rejected approaches. */
    private fun duplicateEscalation(count: Int): String {
        if (count < 2) return ""
        return "WARNING: you have repeated an already-rejected approach $count times. " +
                "Repeating rejected steps only wastes attempts. STOP — pick a fundamentally different approach " +
                "(a different lemma, [CASE]-split on an expression, or [REWRITE] first).\n"
    }

    private fun buildProgressNote(
        history: List<Pair<String, String>>,
        currentError: String,
        currentTerm: String
    ): String {
        if (history.isEmpty()) return ""

        val currentKey = errorKey(currentError)
        val lastKey = errorKey(history.last().second)

        if (currentKey == lastKey) {
            val differentAttempt = history.findLast { errorKey(it.second) != currentKey }
            if (differentAttempt != null) {
                return "REGRESSION WARNING: You are getting the SAME error as before. " +
                        "Your attempt '${differentAttempt.first}' previously got PAST this error — " +
                        "use that expression as your starting point and fix only the remaining issue.\n\n"
            }
            val sameCount = history.count { errorKey(it.second) == currentKey }
            if (sameCount >= 2) {
                return "STUCK: You have hit the SAME error ${sameCount + 1} times in a row. " +
                        "Small variations of this step will not fix it — the STEP ITSELF is wrong. " +
                        "Abandon this approach and try something fundamentally different " +
                        "(a different lemma, [CASE]-split on an expression, or [REWRITE] first).\n\n"
            }
            return ""
        }

        val regressionSource = history.dropLast(1).findLast { errorKey(it.second) == currentKey }
        if (regressionSource != null) {
            val fixAttempt = history.findLast { errorKey(it.second) != currentKey }
            if (fixAttempt != null) {
                return "REGRESSION WARNING: You already had this exact error before and FIXED it with: '${fixAttempt.first}'. " +
                        "You are now regressing. Use '${fixAttempt.first}' as your base and fix only the remaining issue.\n\n"
            }
        }

        val lastTerm = history.last().first
        return "PROGRESS: Your last attempt '$lastTerm' got past the previous error. " +
                "You are now hitting a DIFFERENT error. KEEP the parts of '$lastTerm' that worked and fix ONLY the new issue.\n\n"
    }

    companion object {
        const val INCLUDE_PLANNING_INSTRUCTIONS = true

        /** Matches Arend's FunctionArgInferenceError in both variants:
         *  "Cannot infer parameter 'x' of definition 'f'" (named) and
         *  "Cannot infer the 3rd parameter of definition 'f'" (unnamed). */
        private val ARG_INFERENCE_ERROR =
            Regex("""Cannot infer (parameter '|the \d+(?:st|nd|rd|th) parameter)""")

        /** pmap applied to an identity lambda (any variable name, any paren nesting):
         *  a definitional no-op. */
        private val IDENTITY_PMAP =
            Regex("""pmap\s*\(*\s*\\lam\s+(\S+)\s*=>\s*\1\s*\)*""")
        private fun buildSystemPrompt(): String = """
You are an expert in the Arend proof assistant. Your task is to fill proof holes ({?}) one step at a time.
You will be given the signature of the lemma being proved, the expected type of the current goal, and its context bindings.
""" + (if (!INCLUDE_PLANNING_INSTRUCTIONS) """
Respond with ONLY a step tag. Do NOT explain, plan, or reason. Output the tag immediately.
""" else "") + """

## How to respond

Use one of the following step types:

### 1. [APPLY name] — apply a function, lemma, or constructor
List the argument VALUES you need to provide, one per line, in the order shown in the "provide:" section.
Do NOT write "name: value" — just write the value.
Propositional arguments (equality proofs, proof terms) are ALWAYS automatically filled as {?} subgoals — NEVER provide them; a proof you provide for them is IGNORED.
Only provide non-propositional arguments (data, functions, elements).
To specify implicit arguments, wrap them in {braces}, positionally, in the order shown in the "implicits:" section.
They are inserted before the explicit args. You cannot skip earlier implicits — include ALL of them up to the last one you need to pin.

Example — applying pmap (provide: f):
[APPLY pmap]
\lam x => suc x
[/APPLY]
This constructs: pmap (\lam x => suc x) {?}  — the equality proof becomes a subgoal.

Example — applying inv (no args to provide — the equality is propositional):
[APPLY inv]
[/APPLY]
This constructs: inv {?}

Example — applying byLeft (constructor, no args to provide):
[APPLY byLeft]
[/APPLY]

Dot notation for record/class fields:
[APPLY p.isIrr]
[/APPLY]
This constructs: p.isIrr {?}

Example — specifying implicit arguments:
[APPLY p.isIrr]
{k}
{k|n.inv}
[/APPLY]
This constructs: p.isIrr {k} {k|n.inv} {?}  — implicit x=k, y=k|n.inv, equality auto-filled.

### 2. [REWRITE] — rewrite the goal using an equality
Provide the equality proof. The system constructs: rewrite <proof> {?}

Example — rewrite with a hypothesis:
[REWRITE]p[/REWRITE]
This constructs: rewrite p {?}

Example — rewrite with an inverted equality:
[REWRITE]inv q[/REWRITE]
This constructs: rewrite (inv q) {?}

### 3. [INTRO] — introduce lambda parameters
When the goal is a Pi type or function type, introduce the parameters as a lambda.
Provide the variable names. If omitted, names are extracted from the goal type.

Example — introduce named parameters:
[INTRO]x y[/INTRO]
This constructs: \lam x y => {?}

Example — introduce without explicit names (names extracted from goal type):
[INTRO][/INTRO]
If goal is \Pi (n : Nat) -> P n, this constructs: \lam n => {?}
If goal is A -> B, this constructs: \lam _ => {?}

### 4. [CASE] — case split on a variable or expression
Provide the variable name or expression to case-split on. The system determines the constructors and generates the full \case expression with {?} holes for each branch.
Do NOT write \case yourself — the system constructs it. Do NOT use [APPLY \case] — always use [CASE].
Do NOT use goals {?} in split expression.
For variables, \case \elim is used (substitutes in the return type). For expressions, \case without \elim.

Example — case split on a variable:
[CASE]n[/CASE]
The system generates: \case \elim n \with { | 0 => {?} | suc n => {?} }

Example — case split on an expression:
[CASE]decideEq x y[/CASE]
The system generates: \case decideEq x y \with { | yes p => {?} | no q => {?} }

Example — case split on a function result:
[CASE]p.isIrr (inv k|n.inv-right)[/CASE]
The system generates: \case p.isIrr (inv k|n.inv-right) \with { | byLeft a => {?} | byRight b => {?} }

### 5. [REFINE] — give the step as a term with holes
For steps the tags above cannot express. Write the expression that fills the current {?},
putting {?} everywhere a subproof is left open; each hole becomes one of the next goals.
NEVER write [REFINE]{?}[/REFINE] — a lone hole leaves the goal unchanged and is rejected.

Use it for:
  - a tuple for a \Sigma goal:            [REFINE](mod-lem p {?}, rec-lem p {?})[/REFINE]
  - a projection:                         [REFINE](toSigma t).1[/REFINE]
  - a hole in a NON-FINAL argument:       [REFINE]f {?} k|n[/REFINE]
  - applying the RESULT of a hypothesis:  [REFINE]p.notInv ide-isInv[/REFINE]
  - \let / \have:                         [REFINE]\let d => k|n.inv \in {?}[/REFINE]
  - one \case on SEVERAL expressions:     [REFINE]\case \elim n, p \with { | 0, p => {?} | suc n, p => {?} }[/REFINE]

Prefer [APPLY], [CASE], [INTRO] and [REWRITE] whenever they fit: they fill propositional
arguments and write the case clauses for you. Reach for [REFINE] only when they cannot.

""" + if (INCLUDE_PLANNING_INSTRUCTIONS) planningInstructions() else """""" + """
# Arend Syntax Reference

## Keywords (ALL keywords start with \)
Definition: \func, \lemma, \data, \class, \record, \meta, \axiom, \cons
Expression: \lam, \Pi, \Sigma, \case, \scase, \let, \let!, \have, \in, \with, \elim, \cowith, \return, \new
Type: \Type, \Prop, \Set, \h-Type, \oo-Type
Proof: \path, \coe, \eval, \peval
There is NO \ind, \refl, \intro, \apply, \exact, \tactic, \induction, \destruct, \ih keyword in Arend.

## Core Constructs

Lambda: \lam x => body, \lam (x : A) => body
Pi type: \Pi (x : A) -> B, or just A -> B for non-dependent
Sigma type: \Sigma (x : A) (B x), pairs: (a, b), projections: p.1, p.2
Let: \let x => e \in body  (NOTE: uses =>, NOT =. \let x = e is WRONG syntax)

\case \elim x \with { | pat1 => e1 | pat2 => e2 }
\case \elim x, \elim y \with { | p1, p2 => result }
WARNING: \case x \with (WITHOUT \elim) does NOT substitute x in the return type.
This means idp will FAIL because the type stays unreduced. ALWAYS write \case \elim x \with.

Only use plain \case (without \elim) when matching on a COMPUTED expression, not a variable:
\case f x \with { | pat1 => e1 | pat2 => e2 }

Top-level \elim (for recursive lemmas — passes termination checking):
  \elim x | pat1 => e1 | pat2 => e2
  Use this when the proof calls the lemma being proved recursively (induction).
  Do NOT use \case \elim for recursive calls — it fails termination checking.

## Equality and Paths

a = b is the equality/path type.
idp : a = a (reflexivity).
p @ i applies a path to an interval point.
path (\lam i => f i) constructs a path.
inv p : b = a when p : a = b.
p *> q : a = c when p : a = b and q : b = c (path composition).

pmap f p : f a = f b when p : a = b (congruence).
transport B p b : B a' when p : a = a' and b : B a.

## Building Equality Chains

Both proofs of *> are propositional, so [APPLY *>] with no args leaves the chain midpoint
uninferrable and FAILS with "Cannot infer parameter 'a''". NEVER give the proofs — instead,
pin the path ENDPOINTS as implicit args (in "implicits:" order, starting from the first):
[APPLY *>]
{Nat}
{n}
{k * k|n.inv}
{k}
[/APPLY]
This constructs: *> {Nat} {n} {k * k|n.inv} {k} {?} {?}  — with determined subgoals
n = k * k|n.inv and k * k|n.inv = k, each fillable in the next steps.

Direction matters! In p *> q, the RIGHT side of p must equal the LEFT side of q.
  If p : a = b and q : c = b, you CANNOT compose p *> q. Use p *> inv q instead.
  If p : a = b and q : c = d, check if b = c before composing.

To flip direction: use inv. If p : a = b, then inv p : b = a.
  pmap f p : f a = f b. To get f b = f a, write inv (pmap f p).
  Common pattern: pmap f (inv p) gives f b = f a (flip INSIDE pmap).

Algebra chains: to prove a = d from a = b, c = b, c = d:
  Compose: idp *> inv q *> r, or rewrite with intermediate equalities.

When building a chain, TRACE THE TYPES of each step:
  Step 1: what equality do I have? (e.g., p : x = y)
  Step 2: what do I need? (e.g., goal: a = b)
  Step 3: do the endpoints match? If not, use inv or pmap to align them.

## Records and Classes

Access record fields with dot notation: instance.field, NOT RecordType.field instance.
Records/classes define types with named fields. Given an instance, access fields with dot notation.

LDiv {M : Monoid} — a divisibility witness. If d : LDiv {M} a b, then:
  d.val : M  — the divisor (= a)
  d.inv : M  — the quotient
  d.inv-right : d.val * d.inv = d.elem  — proof that a * quotient = b

Inv {M : Monoid} — an invertibility witness. If j : Inv {M} x, then:
  j.val : M  — the element (= x)
  j.inv : M  — the inverse
  j.inv-left : j.inv * j.val = ide  — left inverse proof
  j.inv-right : j.val * j.inv = ide  — right inverse proof

Irr {M : CMonoid} — an irreducibility witness. If p : Irr e, then:
  p.isIrr {x y : M} (eq : e = x * y) : Inv x || Inv y  — irreducibility condition
  Use as: p.isIrr proofExpr, where proofExpr : e = x * y

Use [APPLY instance.field] to apply field access. Example:
  [APPLY p.isIrr]
  [/APPLY]

## Definitional Equalities in Nat

The typechecker automatically simplifies these (no proof needed, idp works):
  n * 1 = n, 1 * n = n, 0 + n = n, n * 0 = 0, 0 * n = 0
These do NOT simplify (need explicit proof):
  n + 0 = n (requires induction or a lemma)

## Standard Metas (from arend-lib, require imports)

From Paths.Meta (import with \import Paths.Meta):
  rewrite p expr — replaces occurrences of the LHS of p in the goal type, then checks expr
  rewriteI p expr — rewrite with inv p
  ext — proves equality goals (function extensionality, sigma paths, etc.)
  simp_coe — simplifies coe/transport equalities
  simplify — simplifies algebraic expressions in monoids/rings

From Meta (import with \import Meta):
  unfold (f1, ..., fn) expr — unfolds definitions f1..fn in the expected type before checking expr
  mcases \with { | pat => ... } — case splits on all \case expressions in the goal type
  cases (e1, e2) \with { ... } — explicit case analysis
  assumption — searches for a proof in the context

From Function.Meta (import with \import Function.Meta):
  $ — right-associative application (like Haskell)

## Nat (from Prelude)
Constructors: 0 (or zero), suc n
Operations: +, *, Nat.-, Nat.div, Nat.mod, <, <=

## List (from Data.List)
Constructors: nil, :: (cons, right-associative)
Operations: ++ (append)

## Common Proof Patterns

Induction on Nat (recursive — use top-level \elim):
  \elim n | 0 => base | suc n' => step-using-recursive-call

Induction on List (recursive — use top-level \elim):
  \elim l | nil => base | :: a t => step-using-recursive-call

Non-recursive case split (no recursive call needed):
  \case \elim x \with { | pat1 => e1 | pat2 => e2 }

Rewrite chain: rewrite p1 (rewrite p2 idp)
  or: rewrite p1 $ rewrite p2 idp

Congruence: pmap f proof, pmap (\lam x => expr) proof

## Rules

1. {?} is a goal/hole — the typechecker accepts it at ANY type. Never use {?} as the whole expression.
2. All keywords start with \. There are no keywords without \.
3. Pattern matching on a variable ALWAYS needs \elim: \case \elim x \with { | 0 => ... | suc n => ... }. Without \elim, idp WILL FAIL.
4. Constructors are matched by name: | 0 => ..., | suc n => ..., | nil => ..., | :: a t => ...
5. NEVER case-split the same expression twice: a [CASE] on an expression already split in an ancestor branch is REJECTED. The expected type does not change between a case and its own branches — the context only gains the pattern variable — so the repeated split nests forever without progress. Use the hypotheses bound by the branch pattern instead, or split a DIFFERENT expression.
6. Do NOT wrap output in ```arend or any markdown.
7. Do NOT invent keywords. Only use syntax listed above.
8. For induction (recursive calls to the lemma being proved), ALWAYS use top-level \elim, NOT \case \elim.
9. Output ONLY the expression to fill the current {?}. Do NOT repeat the surrounding proof structure.
10. \let uses => (fat arrow), NEVER = (equals sign). Write \let x => e \in body, NOT \let x = e.
11. When a previous attempt fails, fix ONLY the error. Use {?} for subparts you haven't verified. Do NOT try to fill all holes AND fix errors at the same time.
12. When a previous attempt made progress (got a different error), KEEP the parts that worked. Change ONLY the part that caused the new error.
13. NEVER use [APPLY \case] or [APPLY \lam] or [APPLY \let]. For case splitting use [CASE], for lambda introduction use [INTRO], for \let/\have and other terms use [REFINE]. [APPLY] is ONLY for named functions, lemmas, and constructors.
14. NEVER use pmap with an identity function (pmap (\lam x => x) ...) — it is a definitional no-op that re-creates the same goal. Such steps are REJECTED.
""".trimIndent()

        private fun planningInstructions(): String = """
 Before the step tag, output a SHORT plan: 1-2 sentences MAX, naming only the tactic you will use and why. Do NOT restate the goal, context, or background. Keep the total response under 60 words. Then immediately provide the step tag.

Use {?} for subexpressions where a nontrivial proof is expected (but NEVER for the whole expression).

# Error Recovery

When your attempt fails, you MUST: (1) explain the error in ONE sentence, (2) give a ONE-sentence corrected plan, (3) give the corrected step tag. No other text.

## Example: Type mismatch — wrong constructor argument

Context: i<k : i < k
Expected type: suc i < suc k

WRONG guess: i<k
Error: Type mismatch. Expected type: suc i < suc k. Actual type: i < k.

Error explanation: I provided `i<k` which has type `i < k`, but the goal needs `suc i < suc k`. The constructor `suc<suc` wraps `n < m` into `suc n < suc m`.

Corrected plan: Apply `suc<suc` to `i<k`.
[APPLY suc<suc]
[/APPLY]

## Example: Type mismatch — equality is flipped

Context: p : a = b
Expected type: b = a

WRONG guess: p
Error: Type mismatch. Expected type: b = a. Actual type: a = b.

Corrected plan: The equality is flipped. Apply `inv` to reverse it.
[APPLY inv]
[/APPLY]       
    """.trimIndent()
    }


}
