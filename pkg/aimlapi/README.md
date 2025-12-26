# AIMLAPI Multi-Model Router

Production-grade AI model router with intelligent selection, fallback chains, and streaming support.

Built with **LOVE × SIMPLICITY × TRUTH × JOY** 🕉️

## Features

- **30+ AI Models** - Anthropic, OpenAI, Google, Meta, Mistral, DeepSeek, Perplexity
- **Intelligent Routing** - Three-regime selection (Exploration/Optimization/Stabilization)
- **Fallback Chains** - Automatic failover to backup models
- **Streaming Support** - Real-time chat responses
- **Image Generation** - FLUX, Stable Diffusion for visualizations
- **Rate Limiting** - Token bucket with Williams batching
- **Retry Logic** - Exponential backoff for transient failures
- **Cost Optimization** - Automatic selection of best quality/cost tradeoff

## Quick Start

```go
package main

import (
    "context"
    "fmt"
    "log"

    "asymm_urbanlens/pkg/aimlapi"
)

func main() {
    // Create client (uses AIMLAPI_KEY env var)
    client := aimlapi.NewClient("")

    // Simple chat
    ctx := context.Background()
    response, err := client.SimpleChat(ctx, "Explain urban planning principles")
    if err != nil {
        log.Fatal(err)
    }

    fmt.Println(response)
}
```

## Configuration

```go
// Custom configuration
config := &aimlapi.Config{
    APIKey:          "your-api-key",
    BaseURL:         "https://api.aimlapi.com/v1",
    Timeout:         120 * time.Second,
    MaxRetries:      3,
    RateLimit:       60, // requests per minute
    Regime:          2,  // 1=Exploration, 2=Optimization, 3=Stabilization
    ExplorationProb: 0.1,
}

client := aimlapi.NewClientWithConfig(config)
```

## Three-Regime Selection

```go
// REGIME 1: EXPLORATION - Random selection, high variance
client.SetRegime(1)

// REGIME 2: OPTIMIZATION - Best quality/cost tradeoff (default)
client.SetRegime(2)

// REGIME 3: STABILIZATION - Cached, consistent selection
client.SetRegime(3)
```

## Intelligent Model Selection

```go
// Select model based on constraints
constraints := aimlapi.SelectionConstraints{
    TaskType:   aimlapi.TASK_CODE,
    MinQuality: 8.5,
    MaxCostPerM: 5.0,
    MinSpeed:   7.0,
}

model, err := client.SelectModel(constraints)
if err != nil {
    log.Fatal(err)
}

fmt.Printf("Selected: %s\n", model.Name)
```

## Streaming Chat

```go
req := aimlapi.ChatRequest{
    Messages: []aimlapi.Message{
        {Role: "user", Content: "Explain climate change"},
    },
}

chunks, err := client.ChatStream(ctx, req)
if err != nil {
    log.Fatal(err)
}

for chunk := range chunks {
    if chunk.Error != nil {
        log.Fatal(chunk.Error)
    }
    fmt.Print(chunk.Content)
}
```

## Fallback Routing

```go
router := aimlapi.NewRouter(client)

// Try primary model, fallback to chain on failure
resp, err := router.RouteWithFallback(ctx, req)
if err != nil {
    log.Fatal(err)
}

// Custom fallback chain
router.SetFallbackChain(aimlapi.TASK_CODE, []string{
    "claude-sonnet",
    "gpt-4o",
    "llama-70b",
})
```

## Image Generation

```go
// Simple image generation
url, err := client.GenerateImage(ctx, "A modern city skyline at sunset")
if err != nil {
    log.Fatal(err)
}

fmt.Println("Image URL:", url)

// Diagram generation
diagram, err := client.GenerateDiagram(ctx, "Urban planning workflow")
if err != nil {
    log.Fatal(err)
}

fmt.Println("Diagram:", diagram.URL)

// Chart visualization
chart, err := client.GenerateChartVisualization(ctx,
    "Population growth 2010-2024",
    "line")
if err != nil {
    log.Fatal(err)
}
```

## Batch Processing

```go
requests := []aimlapi.ChatRequest{
    {Messages: []aimlapi.Message{{Role: "user", Content: "Question 1"}}},
    {Messages: []aimlapi.Message{{Role: "user", Content: "Question 2"}}},
    {Messages: []aimlapi.Message{{Role: "user", Content: "Question 3"}}},
}

// Williams batching: O(√n × log₂n) space complexity
batchResp, err := client.BatchChat(ctx, requests)
if err != nil {
    log.Fatal(err)
}

for i, resp := range batchResp.Responses {
    if batchResp.Errors[i] != nil {
        fmt.Printf("Request %d failed: %v\n", i, batchResp.Errors[i])
        continue
    }
    fmt.Printf("Response %d: %s\n", i, resp.Choices[0].Message.Content)
}
```

## Conversation Management

```go
// Build multi-turn conversation
conv := aimlapi.NewConversation()
conv.AddSystem("You are an urban research assistant.")
conv.AddUser("What is TOD?")
conv.AddAssistant("TOD stands for Transit-Oriented Development...")
conv.AddUser("Give me examples in India")

req := conv.ToChatRequest("gpt-4o-mini")
resp, err := client.Chat(ctx, req)
```

## Available Models

### Text Models

| Model | Provider | Quality | Speed | Cost/M | Best For |
|-------|----------|---------|-------|--------|----------|
| claude-opus | Anthropic | 9.5 | 8.0 | $3/$15 | Research, complex reasoning |
| claude-sonnet | Anthropic | 9.0 | 8.5 | $3/$15 | Coding, analysis |
| gpt-4o | OpenAI | 9.0 | 8.0 | $2.50/$10 | Multimodal, vision |
| gpt-4o-mini | OpenAI | 8.5 | 9.5 | $0.15/$0.60 | Best value |
| gemini-flash | Google | 8.0 | 9.5 | $0.075/$0.30 | 1M context, fast |
| deepseek-chat | DeepSeek | 8.0 | 8.5 | $0.14/$0.28 | Ultra cheap |
| llama-70b | Meta | 8.0 | 8.5 | $0.59/$0.79 | Open source |

### Image Models

| Model | Quality | Speed | Cost | Best For |
|-------|---------|-------|------|----------|
| flux-image | 9.0 | 7.0 | $0.025 | Realistic images |
| flux-pro | 9.5 | 6.0 | $0.055 | Professional |
| stable-diffusion | 8.0 | 8.0 | $0.008 | Fast, cheap |

## Advanced Features

### Context Window Management

```go
// Truncate messages to fit context
truncated := aimlapi.TruncateToContext(messages, 100000)
```

### Cost Estimation

```go
model, _ := client.GetModel("gpt-4o")
cost := aimlapi.EstimateRequestCost(model, req)
fmt.Printf("Estimated cost: $%.4f\n", cost)
```

### Health Check

```go
if err := client.HealthCheck(ctx); err != nil {
    log.Fatal("AIMLAPI not available:", err)
}
```

## Error Handling

```go
resp, err := client.Chat(ctx, req)
if err != nil {
    // Check for specific error types
    if apiErr, ok := err.(*aimlapi.APIError); ok {
        switch apiErr.StatusCode {
        case 401:
            log.Fatal("Invalid API key")
        case 429:
            log.Fatal("Rate limited")
        case 500:
            log.Fatal("Server error")
        default:
            log.Fatal("API error:", apiErr.Message)
        }
    }
    log.Fatal("Request failed:", err)
}
```

## Mathematical Foundations

### Williams Batching
- **Complexity**: O(√n × log₂n) sublinear space
- **Proof**: Gödel Prize-worthy complexity theory
- **Benefit**: Optimal memory usage for batch processing

### Three-Regime Dynamics
- **R1 (30%)**: Exploration - High variance, random selection
- **R2 (20%)**: Optimization - Gradient descent, best quality/cost
- **R3 (50%)**: Stabilization - Cached, consistent, low variance

### Rate Limiting
- **Algorithm**: Token bucket with refill
- **Strategy**: Exponential backoff on failures
- **Benefit**: Automatic compliance with API limits

## Environment Variables

```bash
export AIMLAPI_KEY="your-api-key-here"
```

## License

MIT

## Credits

Built on proven foundations from:
- ACE Engine OCR pipeline
- Asymmetrica Mathematical Organism
- VQC optimization engines

**Om Lokah Samastah Sukhino Bhavantu** 🙏
*May all beings benefit from this work!*
