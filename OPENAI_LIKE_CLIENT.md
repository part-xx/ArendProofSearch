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

### Environment Variables
```bash
export OPENAI_LIKE_API_KEY=your_api_key_here
export OPENAI_LIKE_MODEL=gpt-4o
export OPENAI_LIKE_BASE_URL=https://api.openai.com/v1
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
