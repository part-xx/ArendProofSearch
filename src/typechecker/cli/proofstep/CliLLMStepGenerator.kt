package typechecker.cli.proofstep

import ai.koog.agents.core.agent.AIAgent
import ai.koog.prompt.llm.LLModel
import kotlinx.coroutines.runBlocking
import org.example.org.jetbrains.ai.kotlin.playbook.createLiteLLMModel
import org.example.org.jetbrains.ai.kotlin.playbook.createLiteLLMPromptExecutor
import org.jetbrains.ai.kotlin.playbook.LITELLM_API_KEY
import org.jetbrains.ai.kotlin.playbook.LITELLM_URL
import typechecker.Proof
import typechecker.ProofStep
import typechecker.ProofStepGenerator
import typechecker.cli.*
import typechecker.coreapi.proofstep.LLMStepGenerator
import java.io.File

class CliLLMStepGenerator(
    private val cli: CliApi,
    private val moduleDef: String,
    liteLLMModelId: String = "openai/gpt-4o",
    private val maxAttempts: Int = 50
) : ProofStepGenerator<PlainTextGoal> {

    private val executor = createLiteLLMPromptExecutor(LITELLM_URL, LITELLM_API_KEY)
    private val llmModel: LLModel = createLiteLLMModel(liteLLMModelId)

    private val systemPrompt = buildSystemPrompt()
    private val preprompt: String

    init {
        val examples = LLMStepGenerator.parseConcatenatedJson(File("src/examples.json"))
        val examplesPrompt = examples.fold("") { acc, map ->
            acc + "\ncontext: ${map["Context"]}\nexpected type: ${map["Expected type"]}" +
                    "\nCORRECT COMPLETION EXPRESSION is: ${map["Expression"]}"
        }
        val examplePremises = HashSet<String>()
        examples.forEach { examplePremises.addAll((it["Premises"] as List<String>).map { "$it\n" }) }
        examplePremises.removeIf { it.contains("fin-last-or") }

        preprompt = "I am going to give you a snippet of code in the formal verification language Arend. " +
                "You have to guess the completion of just one step (definition or tactic application). Use {?} " +
                "for arguments where a nontrivial proof is expected (but not for the whole expression). " +
                "First, output a short plan describing your reasoning for proving the goal. " +
                "Then, suggest the first step. Wrap the term in [TERM] and [/TERM] tags. " +
                "For example:\nPlan: We need to case split on i, then handle each case separately.\n[TERM]\\case \\elim i \\with { | zero => {?} | suc i' => {?} }[/TERM]\n" +
                "Dont create nested cases with the same variable like in the example \\case \\elim i \\with { | zero => \\case \\elim i ...}" +
                "Never use \\case i for individual variables!! Use \\case \\elim i instead!!\n" +
                "Dont wrap your output in anything like ```arend etc. " +
                "Now, I am going to give you examples of such successful completions." +
                "Premises: \n$examplePremises\n" +
                "Examples:\n$examplesPrompt\n"
    }

    override fun generate(goal: PlainTextGoal, currentProof: Proof<PlainTextGoal>?): List<ProofStep<PlainTextGoal>> {
        val currentProofText = (currentProof as? PlainTextProof)?.proofText ?: "{?}"
        val context = goal.contextBindings.joinToString("\n") { "${it.name} : ${it.type}" }

        var currentPrompt = preprompt +
                "provide CORRECT COMPLETION EXPRESSION for \n" +
                "context: $context\nexpected type: ${goal.expectedType}\n" +
                "current proof: $currentProofText\n" +
                "\nReminder: you can use {?} for subexpressions (but not for the whole expression). Dont try to solve everything at once."

        println("Expected type: ${goal.expectedType}")
        println("Context: $context")

        repeat(maxAttempts) { attempt ->
            println("Attempt ${attempt + 1}")
            val agent = AIAgent(
                executor = executor,
                systemPrompt = systemPrompt,
                llmModel = llmModel,
                temperature = 0.7,
            )
            val response = runBlocking { agent.run(currentPrompt) }
            println("The response:\n${response.chunked(120).joinToString("\n")}")

            val term = LLMStepGenerator.extractTermFromResponse(response)
            if (term == null) {
                println("Could not extract term from response")
                currentPrompt += "\n\nYour previous response did not contain a term wrapped in [TERM]...[/TERM] tags. Please provide your answer with the term wrapped in [TERM] and [/TERM] tags."
                return@repeat
            }
            println("Extracted term: $term")

            try {
                val checkResult = cli.checkExpression(moduleDef, goal.id, term)

                if (checkResult.success) {
                    println("typechecked successfully!")
                    val applyResult = cli.applyStep(moduleDef, goal.id, term)
                    if (applyResult.success) {
                        val newGoals = applyResult.goals.map { g ->
                            PlainTextGoal(g.id, g.expectedType, g.context, moduleDef)
                        }
                        val newProof = PlainTextProof(cli, moduleDef, applyResult.proof, newGoals)
                        return listOf(ProofStep(newProof, 1.0))
                    }
                }

                val errors = checkResult.errors
                if (errors.isNotEmpty()) {
                    val errorMsg = errors.joinToString("\n")
                    println("Errors: $errorMsg")
                    currentPrompt += "\n\nPrevious guess: $term\nResulted in errors:\n$errorMsg\n" +
                            "Please provide a CORRECT COMPLETION EXPRESSION wrapped in [TERM]...[/TERM] tags. " +
                            "Reminder: you can use {?} for subexpressions (but not for the whole expression)."
                }
            } catch (e: Exception) {
                println("Exception during validation: ${e.message}")
                currentPrompt += "\n\nPrevious guess: $term\nResulted in error: ${e.message}\n" +
                        "Please provide a CORRECT COMPLETION EXPRESSION wrapped in [TERM]...[/TERM] tags."
            }
        }

        return emptyList()
    }

    companion object {
        private fun buildSystemPrompt(): String {
            return "You are an assistant for writing in the proof assistant language Arend. " +
                    "Answer concisely. Metas are like tactics in Lean."
        }
    }
}
