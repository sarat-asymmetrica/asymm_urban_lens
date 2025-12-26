// Package aimlapi - Utility functions and helpers
package aimlapi

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"math"
	"net/http"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// RATE LIMITER
// ═══════════════════════════════════════════════════════════════════════════

// RateLimiter implements token bucket rate limiting
type RateLimiter struct {
	tokens    chan struct{}
	rate      int           // requests per minute
	interval  time.Duration // time between tokens
	mu        sync.Mutex
	lastToken time.Time
}

// NewRateLimiter creates a new rate limiter
func NewRateLimiter(requestsPerMinute int) *RateLimiter {
	if requestsPerMinute <= 0 {
		requestsPerMinute = 60
	}

	interval := time.Minute / time.Duration(requestsPerMinute)

	rl := &RateLimiter{
		tokens:    make(chan struct{}, requestsPerMinute),
		rate:      requestsPerMinute,
		interval:  interval,
		lastToken: time.Now(),
	}

	// Fill bucket
	for i := 0; i < requestsPerMinute; i++ {
		rl.tokens <- struct{}{}
	}

	// Start refill goroutine
	go rl.refill()

	return rl
}

// Wait blocks until a token is available
func (rl *RateLimiter) Wait(ctx context.Context) error {
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-rl.tokens:
		return nil
	}
}

// refill adds tokens to bucket at regular intervals
func (rl *RateLimiter) refill() {
	ticker := time.NewTicker(rl.interval)
	defer ticker.Stop()

	for range ticker.C {
		select {
		case rl.tokens <- struct{}{}:
			// Token added
		default:
			// Bucket full
		}
	}
}

// Backoff sleeps with exponential backoff
func (rl *RateLimiter) Backoff(attempt int) {
	backoff := time.Duration(math.Pow(2, float64(attempt))) * time.Second
	if backoff > 30*time.Second {
		backoff = 30 * time.Second
	}
	time.Sleep(backoff)
}

// ═══════════════════════════════════════════════════════════════════════════
// RETRY LOGIC
// ═══════════════════════════════════════════════════════════════════════════

// executeChatWithRetry executes chat request with retry logic
func (c *Client) executeChatWithRetry(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	var lastErr error
	maxRetries := 3

	for attempt := 0; attempt < maxRetries; attempt++ {
		// Wait for rate limiter
		if err := c.rateLimiter.Wait(ctx); err != nil {
			return nil, fmt.Errorf("rate limiter error: %w", err)
		}

		resp, err := c.executeChatRequest(ctx, req)
		if err == nil {
			return resp, nil
		}

		lastErr = err

		// Don't retry on client errors (4xx)
		if isClientError(err) {
			break
		}

		// Exponential backoff (only for retryable errors)
		if attempt < maxRetries-1 {
			c.rateLimiter.Backoff(attempt)
		}
	}

	return nil, lastErr
}

// executeChatRequest executes a single chat request
func (c *Client) executeChatRequest(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	// Marshal request
	reqBody, err := json.Marshal(req)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", c.baseURL+"/chat/completions", bytes.NewReader(reqBody))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Content-Type", "application/json")
	httpReq.Header.Set("Authorization", "Bearer "+c.apiKey)

	// Send request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}
	defer resp.Body.Close()

	// Read response body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check status
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Parse response
	var chatResp ChatResponse
	if err := json.Unmarshal(body, &chatResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &chatResp, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// BATCH PROCESSING (WILLIAMS BATCHING)
// ═══════════════════════════════════════════════════════════════════════════

// BatchRequest represents a batch of chat requests
type BatchRequest struct {
	Requests []ChatRequest
}

// BatchResponse represents batch results
type BatchResponse struct {
	Responses []*ChatResponse
	Errors    []error
}

// BatchChat processes multiple requests with Williams batching
// O(√n × log₂n) sublinear space complexity
func (c *Client) BatchChat(ctx context.Context, requests []ChatRequest) (*BatchResponse, error) {
	if len(requests) == 0 {
		return &BatchResponse{}, nil
	}

	// Williams optimal batch size
	batchSize := calculateWilliamsBatchSize(len(requests))

	responses := make([]*ChatResponse, len(requests))
	errors := make([]error, len(requests))

	// Process in Williams-optimal batches
	for batchStart := 0; batchStart < len(requests); batchStart += batchSize {
		batchEnd := batchStart + batchSize
		if batchEnd > len(requests) {
			batchEnd = len(requests)
		}

		batch := requests[batchStart:batchEnd]

		// Process batch concurrently
		var wg sync.WaitGroup
		sem := make(chan struct{}, batchSize)

		for i, req := range batch {
			globalIdx := batchStart + i

			wg.Add(1)
			go func(idx int, request ChatRequest) {
				defer wg.Done()

				// Acquire semaphore
				sem <- struct{}{}
				defer func() { <-sem }()

				resp, err := c.Chat(ctx, request)
				if err != nil {
					errors[idx] = err
				} else {
					responses[idx] = resp
				}
			}(globalIdx, req)
		}

		wg.Wait()
	}

	return &BatchResponse{
		Responses: responses,
		Errors:    errors,
	}, nil
}

// calculateWilliamsBatchSize computes optimal batch size
// Formula: O(√n × log₂n)
func calculateWilliamsBatchSize(n int) int {
	if n <= 0 {
		return 1
	}

	// Williams batching: O(√n × log₂n)
	sqrtN := math.Sqrt(float64(n))
	log2N := math.Log2(float64(n))

	batchSize := int(math.Ceil(sqrtN * log2N))

	// Clamp to reasonable bounds
	if batchSize < 1 {
		batchSize = 1
	}
	if batchSize > 20 {
		batchSize = 20 // Max concurrent for API stability
	}

	return batchSize
}

// ═══════════════════════════════════════════════════════════════════════════
// TOKEN COUNTING (ROUGH ESTIMATES)
// ═══════════════════════════════════════════════════════════════════════════

// EstimateTokens roughly estimates token count from text
// Real tokenization is model-specific; this is a rough approximation
func EstimateTokens(text string) int {
	// Rough estimate: 1 token ≈ 4 characters for English
	// More accurate: use tiktoken library for specific models
	return len(text) / 4
}

// EstimateCost estimates cost for a chat request
func EstimateCost(model *ModelConfig, promptTokens int, completionTokens int) float64 {
	inputCost := float64(promptTokens) / 1_000_000.0 * model.CostPerMInput
	outputCost := float64(completionTokens) / 1_000_000.0 * model.CostPerMOutput
	return inputCost + outputCost
}

// EstimateRequestCost estimates cost from chat request
func EstimateRequestCost(model *ModelConfig, req ChatRequest) float64 {
	totalPromptTokens := 0
	for _, msg := range req.Messages {
		totalPromptTokens += EstimateTokens(msg.Content)
	}

	// Estimate completion tokens (if not specified, use default)
	completionTokens := req.MaxTokens
	if completionTokens == 0 {
		completionTokens = 1000 // Default estimate
	}

	return EstimateCost(model, totalPromptTokens, completionTokens)
}

// ═══════════════════════════════════════════════════════════════════════════
// VALIDATION
// ═══════════════════════════════════════════════════════════════════════════

// ValidateRequest validates a chat request
func ValidateRequest(req ChatRequest) error {
	if req.Model == "" {
		return fmt.Errorf("model is required")
	}

	if len(req.Messages) == 0 {
		return fmt.Errorf("messages cannot be empty")
	}

	// Validate temperature
	if req.Temperature < 0 || req.Temperature > 2.0 {
		return fmt.Errorf("temperature must be between 0 and 2.0")
	}

	// Validate top_p
	if req.TopP < 0 || req.TopP > 1.0 {
		return fmt.Errorf("top_p must be between 0 and 1.0")
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// CONTEXT MANAGEMENT
// ═══════════════════════════════════════════════════════════════════════════

// TruncateToContext truncates messages to fit within context window
func TruncateToContext(messages []Message, maxTokens int) []Message {
	// Keep system message if present
	systemMsg := []Message{}
	restMsgs := messages

	if len(messages) > 0 && messages[0].Role == "system" {
		systemMsg = messages[:1]
		restMsgs = messages[1:]
	}

	// Estimate tokens
	totalTokens := 0
	for _, msg := range systemMsg {
		totalTokens += EstimateTokens(msg.Content)
	}

	// Add messages from end (most recent) until we hit limit
	truncated := []Message{}
	for i := len(restMsgs) - 1; i >= 0; i-- {
		msgTokens := EstimateTokens(restMsgs[i].Content)
		if totalTokens+msgTokens > maxTokens {
			break
		}
		truncated = append([]Message{restMsgs[i]}, truncated...)
		totalTokens += msgTokens
	}

	return append(systemMsg, truncated...)
}

// ═══════════════════════════════════════════════════════════════════════════
// DEBUG HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// PrintModelInfo prints detailed model information
func PrintModelInfo(model *ModelConfig) {
	fmt.Printf("Model: %s (%s)\n", model.Name, model.ModelID)
	fmt.Printf("Provider: %s\n", model.Provider)
	fmt.Printf("Context: %d tokens\n", model.ContextSize)
	fmt.Printf("Speed: %.1f/10\n", model.SpeedRating)
	fmt.Printf("Quality: %.1f/10\n", model.QualityRating)
	fmt.Printf("Cost: $%.2f/$%.2f per 1M tokens (input/output)\n", model.CostPerMInput, model.CostPerMOutput)
	fmt.Printf("Capabilities: %s\n", formatCapabilities(model.Capabilities))
	fmt.Printf("Notes: %s\n", model.Notes)
}

// formatCapabilities formats capability flags as string
func formatCapabilities(caps Capability) string {
	var parts []string
	if caps&TEXT != 0 {
		parts = append(parts, "TEXT")
	}
	if caps&VISION != 0 {
		parts = append(parts, "VISION")
	}
	if caps&CODE != 0 {
		parts = append(parts, "CODE")
	}
	if caps&REASONING != 0 {
		parts = append(parts, "REASONING")
	}
	if caps&SPEECH != 0 {
		parts = append(parts, "SPEECH")
	}
	if caps&IMAGE_GEN != 0 {
		parts = append(parts, "IMAGE_GEN")
	}
	if caps&CREATIVE != 0 {
		parts = append(parts, "CREATIVE")
	}
	if caps&MATH != 0 {
		parts = append(parts, "MATH")
	}

	result := ""
	for i, part := range parts {
		if i > 0 {
			result += ", "
		}
		result += part
	}
	return result
}
