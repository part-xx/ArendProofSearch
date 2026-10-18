# OpenAI-Compatible LLM Client

This directory contains the `OpenAILikeLLMClient` implementation for connecting to any OpenAI-compatible API.

## Overview

The `OpenAILikeLLMClient` class provides a simple interface for interacting with any OpenAI-compatible API endpoint.

### Supported Services

- **OpenAI** - GPT-4o, GPT-4o-mini, GPT-4 Turbo, etc.
- **DeepSeek** - deepseek-chat, deepseek-reasoner
- **Alibaba Cloud Model Studio** - Qwen, DeepSeek (via Alibaba)
- **Groq** - Llama models, Mistral, etc.
- **Together AI** - Various open-source models
- **Any self-hosted OpenAI-compatible server** - Ollama, vLLM, vLLM, etc.

## Configuration

You can configure the client using environment variables, system properties, or directly in code.

## Running the Arend Qwen3-Coder direct-v1 model

The project configuration selects the Q5_K_M export of the Arend fine-tune of
`Qwen/Qwen3-Coder-30B-A3B-Instruct`:

```text
../VM_setup/models/qwen3-coder-30b-a3b-arend-direct-v1-production-20260823-001-q5_k_m.gguf
```

Install llama.cpp first:

```bash
brew install llama.cpp
```

The fine-tune has a versioned prompt contract. Use `qwen3-direct-v1` with batch
candidate generation and provide theorem-specific premises in a JSON string
array or a dataset-style object containing a `Premises` array:

```bash
./gradlew run --args='--cli-mode -L /path/to/arend-lib -m testPS:myTheorem \
  --premises-file /path/to/premises.json'
```

`gradlew run` now receives `llmBackend`, `llmRegime`, `llmCandidateMode`, the
local model settings, proposal limits, and `llmPremisesFile` from Gradle
properties. Explicit CLI flags take precedence over environment variables,
which take precedence over those system properties.

As with the existing CLI proof-search mode, an Arend daemon for that library
must already be running.

This starts `llama-server` on a free loopback port, waits for the model to load,
uses the GGUF's Jinja chat template in explicit non-thinking mode, and stops the
server when search ends. It also uses the export's recommended top-k/top-p/min-p
sampling and Q8 KV cache with flash attention. No API key is needed.

The direct-v1 request is deliberately exact:

```text
system: Generate one Arend proof step. Return one tagged tactic only.
user:   <CONTEXT>...</CONTEXT>
        <GOAL>...</GOAL>
        <PREMISES>...</PREMISES>
```

No generic Arend manual, batch instruction, current-proof text, planning prose,
or checker feedback is appended. Responses containing prose or more than one
tagged tactic are rejected, matching the training-data validator.

Candidate generation has two explicit modes:

- `--candidate-mode iterative` makes repeated requests. Arend checker
  errors and accepted candidates are fed back to request a corrected or different
  tactic. It is available for general instruction and legacy prompt regimes.
- `--candidate-mode batch` requests alternatives in one API call. Instruction models
  receive two completions, each explicitly asked for a short list of distinct tagged
  steps; every tag in both responses is extracted. Duplicate steps and constructed
  terms are removed, and only terms that pass the Arend checker are returned. No
  checker feedback is sent to the model. Direct-v1 keeps the canonical prompt
  unchanged and requests independent native completions.

Batch console output groups identical tactics, reports each unique proposal once
as `ACCEPT`, `REJECT`, or `SKIP`, and ends with aggregate counts. Checker errors
are kept on one diagnostic line; iterative retry instructions are not printed.

`qwen3-direct-v1` requires batch mode because the production dataset contains
direct examples only; it has no trained recovery-history contract.

For an instruction-mode local batch request, the managed llama.cpp server starts two
slots. Direct-v1 uses one slot per raw proposal so `n` never exceeds
llama-server parallelism. The server reserves the configured context for every
slot. `llmMaxAttempts` is the raw proposal budget; `llmMaxCandidates` limits the
validated candidates returned to proof search.

Override it or tune local inference with:

```bash
./gradlew run --args='--cli-mode -L /path/to/arend-lib -m testPS:myTheorem \
  --llm local --regime qwen3-direct-v1 --candidate-mode batch \
  --local-model-path /path/to/model.gguf --local-context-size 8192 \
  --local-max-tokens 512 --premises-file /path/to/premises.json'
```

For rapid shell-level switching, use `AREND_LLM_BACKEND=local|remote`,
`AREND_LLM_REGIME=qwen3-direct-v1|fine-tuned|instruction`, and
`AREND_LLM_CANDIDATE_MODE=iterative|batch`. `LOCAL_AREND_MODEL_PATH` can supply
the local model path, `AREND_LLM_PREMISES_FILE` can supply premises, and
`LLAMA_SERVER` can point to a non-default `llama-server` executable.

The model-backed integration test automatically runs when the neighboring GGUF
is present (the file is about 20 GB):

```bash
./gradlew test --tests 'integration.CliLLMIntegrationTest.llm - full - prime-char-dir'
```

The integration test reads all model/search configuration from Gradle properties.
Set them in `gradle.properties`, or override them with `-P`:

```bash
./gradlew test \
  -PllmBackend=remote \
  -PllmRegime=instruction \
  -PllmCandidateMode=batch \
  --tests 'integration.CliLLMIntegrationTest.llm - full - prime-char-dir'
```

For local inference, the additional properties are `localModelPath`,
`llamaServerExecutable`, `localContextSize`, `localMaxTokens`, and
`localStartupTimeoutSeconds`. Search breadth is controlled by `llmMaxAttempts`
(the batch raw-proposal budget) and `llmMaxCandidates`; sampling is controlled
by `llmBatchTemperature`. `llmPremisesFile` supplies the optional premise JSON.
`arendLibPath` can override the auto-detected neighboring arend-lib checkout.

Use `llmRegime=fine-tuned` only for the legacy Qwen2.5 compact Python-list
prompt. It is not compatible with the Qwen3 direct-v1 model. Use `instruction`
for a general-purpose instruction model and `qwen3-direct-v1` for the Qwen3
Arend production fine-tune.

The compact regime sends an explicit empty system message. This is intentional:
the Qwen GGUF chat template otherwise inserts `You are a helpful assistant.` when
the system role is absent, even though these model weights are non-Instruct.

### Environment Variables
```bash
export OPENAI_LIKE_API_KEY=your_api_key_here
export OPENAI_LIKE_MODEL=gpt-4o
export OPENAI_LIKE_BASE_URL=https://api.openai.com/v1
export AREND_LLM_BACKEND=remote
export AREND_LLM_REGIME=instruction
export AREND_LLM_CANDIDATE_MODE=iterative
```

### System Properties
```bash
-Dopenai.like.api.key=your_api_key_here
-Dopenai.like.model=gpt-4o
-Dopenai.like.base.url=https://api.openai.com/v1
```

### Direct Configuration (Code)
```kotlin
// OpenAI
val client = OpenAILikeLLMClient(
    apiKey = "your_key",
    model = "gpt-4o",
    baseUrl = "https://api.openai.com/v1"
)

// DeepSeek
val client = OpenAILikeLLMClient(
    apiKey = "your_key",
    model = "deepseek-chat",
    baseUrl = "https://api.deepseek.com/v1"
)

// Alibaba Cloud Qwen
val client = OpenAILikeLLMClient(
    apiKey = "your_key",
    model = "qwen-plus",
    baseUrl = "https://dashscope.aliyuncs.com/compatible-mode/v1"
)

// Alibaba Cloud DeepSeek
val client = OpenAILikeLLMClient(
    apiKey = "your_key",
    model = "deepseek-chat",
    baseUrl = "https://dashscope.aliyuncs.com/compatible-mode/v1"
)

// Groq
val client = OpenAILikeLLMClient(
    apiKey = "your_key",
    model = "llama3-70b-8192",
    baseUrl = "https://api.groq.com/openai/v1"
)
```

## Usage

### Creating Client from Environment

```kotlin
val client = OpenAILikeLLMClient.createFromEnvironment()
```

The client will automatically read `OPENAI_LIKE_API_KEY`, `OPENAI_LIKE_MODEL`, and `OPENAI_LIKE_BASE_URL` from environment variables.

### Creating Client with Custom Configuration

```kotlin
val client = OpenAILikeLLMClient(
    apiKey = "your_api_key",
    model = "gpt-4o",
    baseUrl = "https://api.openai.com/v1"  // Optional, defaults to OpenAI
)
```

### Generating a Response

```kotlin
val response = client.generateResponse(
    systemPrompt = "You are a helpful assistant.",
    userPrompt = "What is 2+2?"
)
println(response) // "4"
```

## Integration with Existing Code

To use an OpenAI-compatible API with the existing proof search infrastructure, update your `LLMStepGenerator` or `CliLLMStepGenerator`:

```kotlin
// Replace FallbackLLMClient with OpenAILikeLLMClient
private val llmClient: LLMClient = OpenAILikeLLMClient.createFromEnvironment()
```

## API Reference

### OpenAILikeLLMClient

#### Constructor
```kotlin
OpenAILikeLLMClient(apiKey: String, model: String = "gpt-4o", baseUrl: String = "https://api.openai.com/v1")
```

- `apiKey`: Your API key (OpenAI, DeepSeek, Alibaba Cloud, Groq, etc.)
- `model`: The model ID to use (default: `gpt-4o`)
- `baseUrl`: The API endpoint URL (default: OpenAI's endpoint)

#### Methods

##### generateResponse
```kotlin
suspend fun generateResponse(systemPrompt: String, userPrompt: String, temperature: Double? = null): String
```

Sends a request to the OpenAI-compatible API and returns the generated response.

**Parameters:**
- `systemPrompt`: The system prompt to set the assistant's behavior
- `userPrompt`: The user's prompt/input
- `temperature`: Optional sampling temperature; sent to the API only when non-null

**Returns:** The generated response text

**Throws:** `RuntimeException` if the API call fails or the response cannot be parsed

#### Companion Object Methods

##### createFromEnvironment
```kotlin
companion object {
    fun createFromEnvironment(): OpenAILikeLLMClient
}
```

Creates a client using environment variables or system properties.

## Common Model Names

| Service | Model Name Example |
|---------|-------------------|
| OpenAI | `gpt-4o`, `gpt-4o-mini`, `gpt-4-turbo` |
| DeepSeek | `deepseek-chat`, `deepseek-reasoner` |
| Alibaba Cloud | `qwen-plus`, `qwen-max`, `deepseek-chat` |
| Groq | `llama3-70b-8192`, `mistral-saba-24b`, `gemma2-9b-it` |
| Together AI | `meta-llama/Meta-Llama-3-70B`, `mistralai/Mistral-7B` |

## Error Handling

The client throws `RuntimeException` with descriptive messages for:
- Missing API key
- Invalid API key
- Network errors
- Invalid response format

## References

- [OpenAI API Reference](https://platform.openai.com/docs/api-reference/chat)
- [DeepSeek API Docs](https://api-docs.deepseek.com/)
- [Alibaba Cloud Model Studio Docs](https://help.aliyun.com/zh/model-studio/developer-reference)
- [Groq API Docs](https://console.groq.com/docs/api-reference)
