package org.example.org.jetbrains.ai.kotlin.playbook

import ai.koog.agents.core.agent.AIAgent
import ai.koog.agents.core.agent.config.AIAgentConfig
import ai.koog.agents.core.agent.entity.AIAgentStrategy
import ai.koog.agents.core.dsl.builder.forwardTo
import ai.koog.agents.core.dsl.builder.strategy
import ai.koog.agents.core.dsl.extension.nodeLLMRequest
import ai.koog.agents.core.dsl.extension.onAssistantMessage
import ai.koog.agents.core.tools.ToolRegistry
import ai.koog.agents.utils.use
import ai.koog.prompt.dsl.Prompt
import ai.koog.prompt.executor.clients.openai.OpenAIClientSettings
import ai.koog.prompt.executor.clients.openai.OpenAILLMClient
import ai.koog.prompt.executor.llms.SingleLLMPromptExecutor
import ai.koog.prompt.executor.model.PromptExecutor
import ai.koog.prompt.llm.LLMCapability
import ai.koog.prompt.llm.LLMProvider
import ai.koog.prompt.llm.LLModel
import kotlinx.coroutines.runBlocking
import org.jetbrains.ai.kotlin.playbook.LITELLM_API_KEY
import org.jetbrains.ai.kotlin.playbook.LITELLM_URL

fun runSimpleAgent(
    userPrompt: String,
    systemPrompt: String,
    liteLLMModelId: String,
    apiKey: String = LITELLM_API_KEY,
    modelCapabilities: List<LLMCapability> = getChatModelCapabilities()
): String = runBlocking {
    val agent = AIAgent(
        executor = createLiteLLMPromptExecutor(LITELLM_URL, apiKey),
        systemPrompt = systemPrompt,
        llmModel = createLiteLLMModel(liteLLMModelId, modelCapabilities)
    )

    return@runBlocking agent.run(userPrompt)
}

fun runComplexWorkflowAgent(
    userPrompt: String,
    systemPrompt: String,
    liteLLMModelId: String,
    apiKey: String = LITELLM_API_KEY
): String = runBlocking {
    val executor = createLiteLLMPromptExecutor(LITELLM_URL, apiKey)

    val strategy = strategy("single-llm-call-strategy") {
        val llmRequest by nodeLLMRequest("llm-call")

        edge(nodeStart forwardTo llmRequest)
        edge(llmRequest forwardTo nodeFinish onAssistantMessage { true })
    }

    return@runBlocking runAgentWithStrategy(
        strategy,
        userPrompt,
        systemPrompt,
        executor,
        createLiteLLMModel(
            liteLLMModelId
        )
    )
}

fun createLiteLLMPromptExecutor(baseUrl: String, apiKey: String): PromptExecutor {
    return SingleLLMPromptExecutor(
        OpenAILLMClient(
            apiKey,
            OpenAIClientSettings(
                baseUrl = baseUrl
            )
        )
    )
}

fun createLiteLLMModel(
    liteLLMModelId: String,
    modelCapabilities: List<LLMCapability> = getChatModelCapabilities()
): LLModel {
    return LLModel(
        provider = LLMProvider.OpenAI,
        id = liteLLMModelId,
        capabilities = modelCapabilities
    )
}

fun getChatModelCapabilities(): List<LLMCapability> {
    return listOf(
        LLMCapability.Temperature, LLMCapability.ToolChoice, LLMCapability.Schema.JSON.Full,
        LLMCapability.Speculation, LLMCapability.Tools, LLMCapability.Vision.Image, LLMCapability.Completion,
        LLMCapability.MultipleChoices
    )
}

private suspend fun runAgentWithStrategy(
    strategy: AIAgentStrategy<String, String>,
    userPrompt: String,
    systemPrompt: String,
    promptExecutor: PromptExecutor,
    model: LLModel,
    toolRegistry: ToolRegistry = ToolRegistry {},
    maxAgentIterations: Int = 3
): String {
    val agentId = "agent-with-strategy"

    val agentConfig = AIAgentConfig(
        prompt = Prompt.build("message-processor") {
            system(systemPrompt)
        },
        model = model,
        maxAgentIterations = maxAgentIterations
    )

    val agent = AIAgent(
        id = agentId,
        promptExecutor = promptExecutor,
        strategy = strategy,
        agentConfig = agentConfig,
        toolRegistry = toolRegistry
    )

    return agent.use {
        it.run(userPrompt)
    }
}
