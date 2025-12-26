// Package aimlapi provides a production-grade multi-model router for AIMLAPI
// Built with LOVE × SIMPLICITY × TRUTH × JOY 🕉️
//
// Features:
// - 30+ AI models (Anthropic, OpenAI, Google, Meta, Mistral, etc.)
// - Intelligent routing with fallback chains
// - Image generation (FLUX, Stable Diffusion)
// - Streaming support
// - Rate limiting with Williams batching
// - Exponential backoff retry logic
// - Three-regime selection (Exploration/Optimization/Stabilization)
//
// Built on proven foundations from ACE Engine + Asymmetrica Mathematical Organism
package aimlapi

import (
	"context"
	"fmt"
	"net/http"
	"os"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CLIENT
// ═══════════════════════════════════════════════════════════════════════════

// Client is the main AIMLAPI client
type Client struct {
	apiKey      string
	baseURL     string
	httpClient  *http.Client
	models      map[string]ModelConfig
	rateLimiter *RateLimiter
	mu          sync.RWMutex

	// Three-regime configuration
	regime          int     // 1=Exploration, 2=Optimization, 3=Stabilization
	explorationProb float64 // Probability of exploration in R2/R3
	cachedModel     *ModelConfig
}

// Config configures the AIMLAPI client
type Config struct {
	APIKey          string
	BaseURL         string
	Timeout         time.Duration
	MaxRetries      int
	RateLimit       int // requests per minute
	Regime          int // 1, 2, or 3
	ExplorationProb float64
}

// DefaultConfig returns sensible defaults
func DefaultConfig() *Config {
	return &Config{
		APIKey:          os.Getenv("AIMLAPI_KEY"),
		BaseURL:         "https://api.aimlapi.com/v1",
		Timeout:         120 * time.Second,
		MaxRetries:      3,
		RateLimit:       60, // 60 requests/minute = 1/sec
		Regime:          2,  // Optimization by default
		ExplorationProb: 0.1,
	}
}

// NewClient creates a new AIMLAPI client with default config
func NewClient(apiKey string) *Client {
	config := DefaultConfig()
	if apiKey != "" {
		config.APIKey = apiKey
	}
	return NewClientWithConfig(config)
}

// NewClientWithConfig creates a client with custom configuration
func NewClientWithConfig(config *Config) *Client {
	if config.BaseURL == "" {
		config.BaseURL = "https://api.aimlapi.com/v1"
	}
	if config.Timeout == 0 {
		config.Timeout = 120 * time.Second
	}
	if config.MaxRetries == 0 {
		config.MaxRetries = 3
	}
	if config.RateLimit == 0 {
		config.RateLimit = 60
	}
	if config.Regime == 0 {
		config.Regime = 2
	}
	if config.ExplorationProb == 0 {
		config.ExplorationProb = 0.1
	}

	return &Client{
		apiKey:  config.APIKey,
		baseURL: config.BaseURL,
		httpClient: &http.Client{
			Timeout: config.Timeout,
		},
		models:          buildModelRegistry(),
		rateLimiter:     NewRateLimiter(config.RateLimit),
		regime:          config.Regime,
		explorationProb: config.ExplorationProb,
	}
}

// IsConfigured returns true if API key is set
func (c *Client) IsConfigured() bool {
	return c.apiKey != ""
}

// SetRegime changes the three-regime mode
// 1 = Exploration (high variance, random selection)
// 2 = Optimization (gradient descent, best quality/cost)
// 3 = Stabilization (cached, consistent selection)
func (c *Client) SetRegime(regime int) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if regime >= 1 && regime <= 3 {
		c.regime = regime
	}
}

// GetRegime returns current regime
func (c *Client) GetRegime() int {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return c.regime
}

// ═══════════════════════════════════════════════════════════════════════════
// CHAT COMPLETION
// ═══════════════════════════════════════════════════════════════════════════

// Chat sends a chat completion request
func (c *Client) Chat(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	if !c.IsConfigured() {
		return nil, fmt.Errorf("AIMLAPI not configured - set AIMLAPI_KEY environment variable")
	}

	// If no model specified, select intelligently
	if req.Model == "" {
		constraints := SelectionConstraints{
			TaskType:   TASK_CHAT,
			MinQuality: 8.0,
		}
		model, err := c.SelectModel(constraints)
		if err != nil {
			return nil, fmt.Errorf("model selection failed: %w", err)
		}
		req.Model = model.ModelID
	}

	// Apply defaults
	if req.Temperature == 0 {
		req.Temperature = 0.7
	}
	if req.MaxTokens == 0 {
		req.MaxTokens = 4000
	}

	// Execute with retry logic
	return c.executeChatWithRetry(ctx, req)
}

// SimpleChat is a convenience wrapper for basic chat
func (c *Client) SimpleChat(ctx context.Context, userMessage string) (string, error) {
	req := ChatRequest{
		Messages: []Message{
			{Role: "user", Content: userMessage},
		},
	}

	resp, err := c.Chat(ctx, req)
	if err != nil {
		return "", err
	}

	if len(resp.Choices) == 0 {
		return "", fmt.Errorf("no choices in response")
	}

	return resp.Choices[0].Message.Content, nil
}

// SystemChat sends a chat with system prompt
func (c *Client) SystemChat(ctx context.Context, systemPrompt, userMessage string) (string, error) {
	req := ChatRequest{
		Messages: []Message{
			{Role: "system", Content: systemPrompt},
			{Role: "user", Content: userMessage},
		},
	}

	resp, err := c.Chat(ctx, req)
	if err != nil {
		return "", err
	}

	if len(resp.Choices) == 0 {
		return "", fmt.Errorf("no choices in response")
	}

	return resp.Choices[0].Message.Content, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// STREAMING
// ═══════════════════════════════════════════════════════════════════════════

// ChatStream sends a streaming chat request
func (c *Client) ChatStream(ctx context.Context, req ChatRequest) (<-chan StreamChunk, error) {
	if !c.IsConfigured() {
		return nil, fmt.Errorf("AIMLAPI not configured - set AIMLAPI_KEY environment variable")
	}

	// If no model specified, select intelligently
	if req.Model == "" {
		constraints := SelectionConstraints{
			TaskType:   TASK_CHAT,
			MinQuality: 8.0,
		}
		model, err := c.SelectModel(constraints)
		if err != nil {
			return nil, fmt.Errorf("model selection failed: %w", err)
		}
		req.Model = model.ModelID
	}

	// Apply defaults
	if req.Temperature == 0 {
		req.Temperature = 0.7
	}
	if req.MaxTokens == 0 {
		req.MaxTokens = 4000
	}

	// Force streaming
	req.Stream = true

	// Execute streaming request
	return c.executeStreamingRequest(ctx, req)
}

// ═══════════════════════════════════════════════════════════════════════════
// IMAGE GENERATION
// ═══════════════════════════════════════════════════════════════════════════

// GenerateImage generates an image from a text prompt
// Returns URL to generated image
func (c *Client) GenerateImage(ctx context.Context, prompt string) (string, error) {
	return c.GenerateImageWithModel(ctx, "flux/dev", prompt)
}

// GenerateImageWithModel generates image with specific model
func (c *Client) GenerateImageWithModel(ctx context.Context, model, prompt string) (string, error) {
	if !c.IsConfigured() {
		return "", fmt.Errorf("AIMLAPI not configured - set AIMLAPI_KEY environment variable")
	}

	req := ImageRequest{
		Model:  model,
		Prompt: prompt,
		N:      1,
		Size:   "1024x1024",
	}

	resp, err := c.executeImageRequestWithRetry(ctx, req)
	if err != nil {
		return "", err
	}

	if len(resp.Data) == 0 {
		return "", fmt.Errorf("no images generated")
	}

	return resp.Data[0].URL, nil
}

// GenerateVisualization creates a visualization from concept + style
func (c *Client) GenerateVisualization(ctx context.Context, concept, style string) (*ImageResult, error) {
	prompt := fmt.Sprintf("Create a %s visualization of: %s", style, concept)
	url, err := c.GenerateImage(ctx, prompt)
	if err != nil {
		return nil, err
	}

	return &ImageResult{
		URL:    url,
		Width:  1024,
		Height: 1024,
	}, nil
}

// GenerateDiagram creates a diagram from description
func (c *Client) GenerateDiagram(ctx context.Context, description string) (*ImageResult, error) {
	prompt := fmt.Sprintf("Create a clear, professional diagram showing: %s. Use clean lines, labels, and logical layout.", description)
	url, err := c.GenerateImage(ctx, prompt)
	if err != nil {
		return nil, err
	}

	return &ImageResult{
		URL:    url,
		Width:  1024,
		Height: 1024,
	}, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// MODEL MANAGEMENT
// ═══════════════════════════════════════════════════════════════════════════

// ListModels returns all available models
func (c *Client) ListModels() []ModelConfig {
	c.mu.RLock()
	defer c.mu.RUnlock()

	models := make([]ModelConfig, 0, len(c.models))
	for _, model := range c.models {
		models = append(models, model)
	}
	return models
}

// GetModel retrieves a specific model by ID
func (c *Client) GetModel(modelID string) (*ModelConfig, error) {
	c.mu.RLock()
	defer c.mu.RUnlock()

	if model, ok := c.models[modelID]; ok {
		return &model, nil
	}

	return nil, fmt.Errorf("model not found: %s", modelID)
}

// ═══════════════════════════════════════════════════════════════════════════
// HEALTH CHECK
// ═══════════════════════════════════════════════════════════════════════════

// HealthCheck verifies API connectivity
func (c *Client) HealthCheck(ctx context.Context) error {
	if !c.IsConfigured() {
		return fmt.Errorf("AIMLAPI not configured")
	}

	// Simple request to models endpoint
	req, err := http.NewRequestWithContext(ctx, "GET", c.baseURL+"/models", nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Authorization", "Bearer "+c.apiKey)

	resp, err := c.httpClient.Do(req)
	if err != nil {
		return fmt.Errorf("health check failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("API returned status %d", resp.StatusCode)
	}

	return nil
}
