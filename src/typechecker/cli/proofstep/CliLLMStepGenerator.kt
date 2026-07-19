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
import typechecker.OpenAILikeLLMClient

import java.io.File

// Gradle properties - read from gradle.properties file
val openaiLikeApiKey: String = System.getenv("OPENAI_LIKE_API_KEY") ?: loadProperty("openaiLikeApiKey") ?: ""
val openaiLikeBaseUrl: String = System.getenv("OPENAI_LIKE_BASE_URL") ?: loadProperty("openaiLikeBaseUrl") ?: ""
val openaiLikeModel: String = System.getenv("OPENAI_LIKE_MODEL") ?: loadProperty("openaiLikeModel") ?: ""

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
    // liteLLMModelId: String = "openai/gpt-4o",
    private val maxAttempts: Int = 50
) : ProofStepGenerator<PlainTextGoal> {

    // LLM dependencies - commented out for build
    // Uncomment later to use JetBrains/koog or other LLM backend
    //private val executor = createLiteLLMPromptExecutor(LITELLM_URL, LITELLM_API_KEY)
    //private val llmModel: LLModel = createLiteLLMModel(liteLLMModelId)
    private val llmClient: LLMClient = OpenAILikeLLMClient(
        apiKey = openaiLikeApiKey,
        model = openaiLikeModel,
        baseUrl = openaiLikeBaseUrl
    )

    private val sigInfoCache = mutableMapOf<String, SignatureInfoResponse>()
    private val systemPrompt = buildSystemPrompt()
    private val preprompt: String
    private val lemmaSignature: String = cli.signature(moduleDef)

    init {
        val modulePrefix = moduleDef.substringBefore(":")
        val moduleDefinitions = buildModuleDefinitions(modulePrefix)

        fetchPremiseSignatures()

        val premisesBlock = if (premises.isNotEmpty())
            "Available functions (use [APPLY name] to apply):\n${formatPremises()}\n"
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
            val info = cli.signatureInfo(moduleDef, name)
            if (info != null) sigInfoCache[name] = info

            if (isRecordClassOrData(premise)) {
                for (fieldName in extractFieldNames(premise)) {
                    if (fieldName !in sigInfoCache) {
                        val fieldInfo = cli.signatureInfo(moduleDef, fieldName)
                        if (fieldInfo != null) sigInfoCache[fieldName] = fieldInfo
                    }
                }
            }
        }
    }

    private fun extractPremiseName(premise: String): String? {
        val match = Regex("""(?:\\truncated\s+)?\\(?:func|lemma|meta|data|class|record)\s+(?:\\[a-z]+\s+\d+\s+)?(\S+)""").find(premise)
        return match?.groupValues?.get(1)
    }

    private fun isRecordClassOrData(premise: String): Boolean {
        val trimmed = premise.trimStart()
        return trimmed.startsWith("\\class") || trimmed.startsWith("\\record") ||
                trimmed.startsWith("\\data") || trimmed.startsWith("\\truncated")
    }

    private fun extractFieldNames(premise: String): List<String> {
        return Regex("""^\s*\|\s+(\S+)""", RegexOption.MULTILINE)
            .findAll(premise)
            .map { it.groupValues[1] }
            .toList()
    }

    private fun formatPremises(): String {
        return premises.map { premise ->
            val name = extractPremiseName(premise)
            val info = name?.let { sigInfoCache[it] }
            if (info != null && info.resultType != null) {
                formatPremiseWithInfo(name, info)
            } else {
                "  $premise"
            }
        }.joinToString("\n")
    }

    private fun formatPremiseWithInfo(name: String, info: SignatureInfoResponse): String {
        val explicitParams = info.params.filter { it.explicit }

        val provideArgs = explicitParams
            .filter { !it.propositional }
            .joinToString(", ") { "${it.name}: ${it.type}" }
        val subgoalArgs = explicitParams
            .filter { it.propositional }
            .joinToString(", ") { "${it.name}: ${it.type}" }
        val resultStr = info.resultType ?: "?"

        val parts = mutableListOf<String>()
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

        val implicitArgs = providedArgs.filter { it.startsWith("{") && it.endsWith("}") }
        val explicitProvided = providedArgs.filter { !(it.startsWith("{") && it.endsWith("}")) }

        val parts = mutableListOf(name)
        parts.addAll(implicitArgs)

        var argIdx = 0
        for (param in explicitParams) {
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

    override fun generate(goal: PlainTextGoal, currentProof: Proof<PlainTextGoal>?): List<ProofStep<PlainTextGoal>> {
        val currentProofText = (currentProof as? PlainTextProof)?.proofText ?: "{?}"
        val context = goal.contextBindings.joinToString("\n") { "${it.name} : ${it.type}" }

        var currentPrompt = preprompt +
                "Signature: $lemmaSignature\n" +
                "Context: $context\n" +
                "Expected type: ${goal.expectedType}\n" +
                "Current proof: $currentProofText\n" +
                "\nProvide CORRECT COMPLETION EXPRESSION."

        println("Expected type: ${goal.expectedType}")
        println("Context: $context")

        val failedAttempts = mutableSetOf<String>()
        val attemptHistory = mutableListOf<Pair<String, String>>()
        var temperature = 0.7

        repeat(maxAttempts) { attempt ->
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
            val response = runBlocking { llmClient.generateResponse(systemPrompt, currentPrompt) }
            println("The response:\n${response.chunked(120).joinToString("\n")}")

            if (response in failedAttempts) {
                println("DUPLICATE — already tried this expression, raising temperature")
                temperature = minOf(temperature + 0.1, 1.0)
                currentPrompt += "\n\nYou already tried: $response\nThis EXACT response was already rejected. " +
                        //              "Explain why your previous approaches failed, then describe a FUNDAMENTALLY DIFFERENT strategy. " +
                        "Provide your new attempt."
                return@repeat
            }

            val step = parseStepFromResponse(response)
            if (step == null) {
                println("Could not extract step from response")
                currentPrompt += "\n\nYour previous response did not contain a valid step. " +
                        "Use [APPLY name]...[/APPLY], [REWRITE]...[/REWRITE], [CASE]...[/CASE], or [INTRO]...[/INTRO]. " +
                        "Do NOT use ```arend code blocks."
                return@repeat
            }

            val term = when (step.type) {
                "apply" -> {
                    val name = step.name!!
                    val constructed = buildTermFromApply(name, step.args)
                    if (constructed != null) {
                        println("Constructed from APPLY: $constructed")
                        constructed
                    } else {
                        val rawArgs = step.args.joinToString(" ") { v ->
                            if (v.startsWith("{") && v.endsWith("}")) v
                            else if (v.contains(' ') || v.startsWith("\\")) "($v)" else v
                        }
                        val result = "$name $rawArgs".trim()
                        println("Constructed from APPLY (raw): $result")
                        result
                    }
                }
                "rewrite" -> {
                    val eq = step.rawTerm!!
                    val result = if (eq.contains(' ') || eq.startsWith("\\")) "rewrite ($eq) {?}" else "rewrite $eq {?}"
                    println("Constructed from REWRITE: $result")
                    result
                }
                "case" -> {
                    val splitExpr = step.rawTerm!!
                    val binding = goal.contextBindings.find { it.name == splitExpr }

                    val cliResponse = cli.typeExpr(moduleDef, goal.id, splitExpr) ?: run {
                        println("CLI invocation error for '$splitExpr'")
                        return emptyList()
                    }

                    if (cliResponse.error != null) {
                        println("Using case with split expression '$splitExpr' resulted in error: ${cliResponse.error}")
                        currentPrompt += "\n\nTypechecking split expression $splitExpr resulted in error: ${cliResponse.error}\n\n" +
                                // "In 1-2 sentences, explain what caused this error. " +
                                // "Then, write a corrected plan. Keep parts that worked. " +
                                "Provide your next attempt."
                        failedAttempts.add(response)
                        return@repeat
                    }

                    val typeName = cliResponse.data?.datatype?.typename ?: run {
                        println("Cannot recognize the type of '$splitExpr' as a datatype")
                        currentPrompt += "\n\nCannot recognize the type of '$splitExpr' as a datatype\n\n" +
                                // "In 1-2 sentences, explain what caused this error. " +
                                // "Then, write a corrected plan. Keep parts that worked. " +
                                "Provide your next attempt."
                        failedAttempts.add(response)
                        return@repeat
                    }
                    val dataModule = cliResponse.data.datatype.module
                    val isVariable = binding != null
                    val isTopLevel = currentProofText.trim() == "{?}"
                    val result = buildCaseExpression(splitExpr, typeName, dataModule, topLevel = isTopLevel, isVariable = isVariable)
                    println("Constructed from CASE: $result")
                    result ?: run {
                        println("Could not build case expression for '${splitExpr}'")
                        currentPrompt += "\n\nCould not build case expression for '${splitExpr}'\n\n" +
                                // "In 1-2 sentences, explain what caused this error. " +
                                // "Then, write a corrected plan. Keep parts that worked. " +
                                "Provide your next attempt."
                        failedAttempts.add(response)
                        return@repeat
                    }
                }
                "intro" -> {
                    val result = buildIntroExpression(step.args, goal)
                    println("Constructed from INTRO: $result")
                    result
                }
                else -> {
                    println("Unknown step type: ${step.type}")
                    return@repeat
                }
            }
            println("Final term: $term")

            val normalizedTerm = term.replace("\\s+".toRegex(), " ").trim()
            if (normalizedTerm in failedAttempts) {
                println("DUPLICATE — already tried this expression, raising temperature")
                temperature = minOf(temperature + 0.1, 1.0)
                currentPrompt += "\n\nYou already tried: $term\nThis EXACT expression was already rejected. " +
          //              "Explain why your previous approaches failed, then describe a FUNDAMENTALLY DIFFERENT strategy. " +
                        "Provide your new attempt."
                return@repeat
            }

            val goalIndex = goal.id.toIntOrNull() ?: 0
            val wrappedTerm = if (term.contains(' ')) "($term)" else term
            val fullBody = PlainTextProof.replaceNthGoal(currentProofText, goalIndex, wrappedTerm)
            if (fullBody == null) {
                println("Could not find goal ${goal.id} in proof text")
                return@repeat
            }

            try {
                val applyResult = cli.applyStep(moduleDef, fullBody)
                if (applyResult.success) {
                    println("applyStep succeeded! Proof: $fullBody")
                    val newGoals = applyResult.goals.map { g ->
                        PlainTextGoal(g.id, g.expectedType, g.context, moduleDef)
                    }
                    val newProof = PlainTextProof(cli, moduleDef, fullBody, newGoals)
                    return listOf(ProofStep(newProof, 1.0))
                }

                val errors = applyResult.errors
                if (errors.isNotEmpty()) {
                    failedAttempts.add(normalizedTerm)
                    val errorMsg = errors.joinToString("\n")
                    println("Errors: $errorMsg")

                    val progressNote = buildProgressNote(attemptHistory, errorMsg, term)
                    attemptHistory.add(Pair(term, errorMsg))

                    val inferenceHint = if (errorMsg.contains("Cannot infer parameter"))
                        "\nHINT: To fix 'Cannot infer parameter X', provide it as an implicit arg wrapped in {braces} in your [APPLY] step. " +
                        "Example: [APPLY natUnit] {k} [/APPLY] constructs natUnit {k} {?}.\n"
                    else ""

                    currentPrompt += "\n\n${progressNote}WRONG guess (#${failedAttempts.size}): $term\nErrors:\n$errorMsg\n$inferenceHint\n" +
                            "Provide your corrected attempt."
                }
            } catch (e: Exception) {
                failedAttempts.add(normalizedTerm)
                val errorMsg = e.message ?: "unknown error"
                println("Exception during validation: $errorMsg")

                val progressNote = buildProgressNote(attemptHistory, errorMsg, term)
                attemptHistory.add(Pair(term, errorMsg))

                currentPrompt += "\n\n${progressNote}Previous guess: $term\nResulted in error: $errorMsg\n\n" +
            //            "In 1-2 sentences, explain what caused this error. " +
            //            "Then, write a corrected plan. Keep parts that worked. " +
                        "Provide your next attempt."
            }
        }

        return emptyList()
    }

    private fun errorKey(error: String): String {
        return error.lines()
            .filter { it.trimStart().startsWith("Expected type:") || it.trimStart().startsWith("Actual type:") }
            .joinToString("\n") { it.trim() }
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
        const val INCLUDE_PLANNING_INSTRUCTIONS = false
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
Propositional arguments (equality proofs, proof terms) are ALWAYS automatically filled as {?} subgoals — do NOT provide them.
Only provide non-propositional arguments (data, functions, elements).
To specify implicit arguments, wrap them in {braces}. They are inserted before the explicit args.

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
5. Do NOT nest \case on the same variable.
6. Do NOT wrap output in ```arend or any markdown.
7. Do NOT invent keywords. Only use syntax listed above.
8. For induction (recursive calls to the lemma being proved), ALWAYS use top-level \elim, NOT \case \elim.
9. Output ONLY the expression to fill the current {?}. Do NOT repeat the surrounding proof structure.
10. \let uses => (fat arrow), NEVER = (equals sign). Write \let x => e \in body, NOT \let x = e.
11. When a previous attempt fails, fix ONLY the error. Use {?} for subparts you haven't verified. Do NOT try to fill all holes AND fix errors at the same time.
12. When a previous attempt made progress (got a different error), KEEP the parts that worked. Change ONLY the part that caused the new error.
13. NEVER use [APPLY \case] or [APPLY \lam] or [APPLY \let]. For case splitting use [CASE], for lambda introduction use [INTRO]. [APPLY] is ONLY for named functions, lemmas, and constructors.
""".trimIndent()

        private fun planningInstructions(): String = """
 First, output a short plan explaining your strategy. Then provide the step.

Use {?} for subexpressions where a nontrivial proof is expected (but NEVER for the whole expression).

# Error Recovery

When your attempt fails, you MUST: (1) explain the error in 1-2 sentences, (2) write a corrected plan, (3) give the corrected step.

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
