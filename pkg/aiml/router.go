// Package aiml provides AI model routing via AIMLAPI
// Ported from indra_conductor for Urban Lens
// 30+ models, three-regime selection, OpenAI-compatible API
package aiml

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math"
	"math/rand"
	"net/http"
	"os"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CORE TYPES
// ═══════════════════════════════════════════════════════════════════════════

const (
	AIMLAPI_BASE  = "https://api.aimlapi.com/v1"
	DEFAULT_MODEL = "gpt-4o-mini"
	MAX_RETRIES   = 3
	RATE_LIMIT    = 100
)

// Capability flags
type Capability int

const (
	TEXT      Capability = 1 << 0
	VISION    Capability = 1 << 1
	CODE      Capability = 1 << 2
	REASONING Capability = 1 << 3
	SPEECH    Capability = 1 << 4
	IMAGE_GEN Capability = 1 << 5
	CREATIVE  Capability = 1 << 6
	MATH      Capability = 1 << 7
)

// Model represents an AI model in our registry
type Model struct {
	ID             string     `json:"id"`
	Name           string     `json:"name"`
	Provider       string     `json:"provider"`
	Capabilities   Capability `json:"capabilities"`
	ContextSize    int        `json:"context_size"`
	SpeedRating    float64    `json:"speed_rating"`
	QualityRating  float64    `json:"quality_rating"`
	CostPerMInput  float64    `json:"cost_per_m_input"`
	CostPerMOutput float64    `json:"cost_per_m_output"`
	UseCases       []string   `json:"use_cases"`
	Notes          string     `json:"notes"`
}

// TaskType defines the type of task
type TaskType string

const (
	TASK_CHAT      TaskType = "chat"
	TASK_CODE      TaskType = "code"
	TASK_VISION    TaskType = "vision"
	TASK_REASONING TaskType = "reasoning"
	TASK_CREATIVE  TaskType = "creative"
	TASK_MATH      TaskType = "math"
	TASK_SPEECH    TaskType = "speech"
	TASK_IMAGE_GEN TaskType = "image_gen"
)

// SelectionConstraints defines requirements for model selection
type SelectionConstraints struct {
	TaskType          TaskType
	MaxCostPerM       float64
	MinSpeed          float64
	MinQuality        float64
	MinContext        int
	PreferredProvider string
}

// ═══════════════════════════════════════════════════════════════════════════
// MODEL REGISTRY - Research-focused selection
// ═══════════════════════════════════════════════════════════════════════════

var ModelRegistry = []Model{
	// Cost-effective options for research
	{
		ID:             "gpt-4o-mini",
		Name:           "GPT-4o Mini",
		Provider:       "OpenAI",
		Capabilities:   TEXT | CODE | REASONING | MATH | VISION,
		ContextSize:    128000,
		SpeedRating:    9.5,
		QualityRating:  8.5,
		CostPerMInput:  0.15,
		CostPerMOutput: 0.60,
		UseCases:       []string{"research", "analysis", "coding", "general"},
		Notes:          "Best value for research tasks",
	},
	{
		ID:             "gpt-4o",
		Name:           "GPT-4o",
		Provider:       "OpenAI",
		Capabilities:   TEXT | CODE | REASONING | MATH | VISION | CREATIVE,
		ContextSize:    128000,
		SpeedRating:    8.0,
		QualityRating:  9.0,
		CostPerMInput:  2.50,
		CostPerMOutput: 10.00,
		UseCases:       []string{"complex analysis", "multimodal", "research"},
		Notes:          "Flagship omni-model",
	},
	{
		ID:             "claude-3-5-sonnet-20241022",
		Name:           "Claude 3.5 Sonnet",
		Provider:       "Anthropic",
		Capabilities:   TEXT | CODE | REASONING | MATH | VISION | CREATIVE,
		ContextSize:    200000,
		SpeedRating:    8.0,
		QualityRating:  9.5,
		CostPerMInput:  3.00,
		CostPerMOutput: 15.00,
		UseCases:       []string{"research", "creative writing", "complex coding"},
		Notes:          "Excellent for nuanced research tasks",
	},
	{
		ID:             "deepseek-chat",
		Name:           "DeepSeek Chat",
		Provider:       "DeepSeek",
		Capabilities:   TEXT | CODE | REASONING | MATH,
		ContextSize:    128000,
		SpeedRating:    8.5,
		QualityRating:  8.0,
		CostPerMInput:  0.14,
		CostPerMOutput: 0.28,
		UseCases:       []string{"cost-effective", "reasoning", "coding"},
		Notes:          "Extremely cost-effective for high-volume research",
	},
	{
		ID:             "gemini-1.5-flash",
		Name:           "Gemini 1.5 Flash",
		Provider:       "Google",
		Capabilities:   TEXT | CODE | VISION | REASONING,
		ContextSize:    1000000,
		SpeedRating:    9.5,
		QualityRating:  8.0,
		CostPerMInput:  0.075,
		CostPerMOutput: 0.30,
		UseCases:       []string{"long documents", "fast responses", "multimodal"},
		Notes:          "1M context, ultra-fast",
	},
	{
		ID:             "llama-3.1-70b-versatile",
		Name:           "Llama 3.1 70B",
		Provider:       "Meta/Groq",
		Capabilities:   TEXT | CODE | MATH,
		ContextSize:    128000,
		SpeedRating:    9.0,
		QualityRating:  8.0,
		CostPerMInput:  0.59,
		CostPerMOutput: 0.79,
		UseCases:       []string{"open source", "general tasks"},
		Notes:          "Open-source flagship via Groq",
	},
}

// ═══════════════════════════════════════════════════════════════════════════
// MODEL ROUTER
// ═══════════════════════════════════════════════════════════════════════════

type Router struct {
	APIKey       string
	BaseURL      string
	HTTPClient   *http.Client
	RateLimiter  chan struct{}
	RegimeMode   int
	CachedModel  *Model
	ExplorationP float64
}

// NewRouter creates a new router with API key from env or default
func NewRouter(apiKey string) *Router {
	if apiKey == "" {
		apiKey = os.Getenv("AIMLAPI_KEY")
	}
	if apiKey == "" {
		apiKey = os.Getenv("OPENAI_API_KEY")
	}

	return &Router{
		APIKey:  apiKey,
		BaseURL: AIMLAPI_BASE,
		HTTPClient: &http.Client{
			Timeout: 120 * time.Second,
		},
		RateLimiter:  make(chan struct{}, RATE_LIMIT),
		RegimeMode:   2, // Default to R2 (Optimization) for research
		ExplorationP: 0.10,
	}
}

// NewRouterWithKey creates router with explicit key
func NewRouterWithKey(apiKey string) *Router {
	return &Router{
		APIKey:  apiKey,
		BaseURL: AIMLAPI_BASE,
		HTTPClient: &http.Client{
			Timeout: 120 * time.Second,
		},
		RateLimiter:  make(chan struct{}, RATE_LIMIT),
		RegimeMode:   2,
		ExplorationP: 0.10,
	}
}

// IsConfigured returns true if API key is set
func (r *Router) IsConfigured() bool {
	return r.APIKey != ""
}

// ═══════════════════════════════════════════════════════════════════════════
// THREE-REGIME SELECTION
// ═══════════════════════════════════════════════════════════════════════════

func (r *Router) SelectModel(constraints SelectionConstraints) (*Model, error) {
	rand.Seed(time.Now().UnixNano())

	if r.RegimeMode == 1 || rand.Float64() < r.ExplorationP {
		return r.exploreModel(constraints)
	}

	if r.RegimeMode == 2 {
		return r.optimizeModel(constraints)
	}

	if r.CachedModel != nil && r.modelMeetsConstraints(r.CachedModel, constraints) {
		return r.CachedModel, nil
	}

	return r.optimizeModel(constraints)
}

func (r *Router) exploreModel(constraints SelectionConstraints) (*Model, error) {
	candidates := r.filterModels(constraints)
	if len(candidates) == 0 {
		return &ModelRegistry[0], nil // Default to first model
	}
	selected := candidates[rand.Intn(len(candidates))]
	r.CachedModel = &selected
	return &selected, nil
}

func (r *Router) optimizeModel(constraints SelectionConstraints) (*Model, error) {
	candidates := r.filterModels(constraints)
	if len(candidates) == 0 {
		return &ModelRegistry[0], nil
	}

	var bestModel *Model
	var bestScore float64 = -1.0

	for i := range candidates {
		model := &candidates[i]
		costScore := 0.5
		if constraints.MaxCostPerM > 0 {
			avgCost := (model.CostPerMInput + model.CostPerMOutput) / 2.0
			costScore = 1.0 - (avgCost / constraints.MaxCostPerM)
			if costScore < 0 {
				costScore = 0
			}
		}

		score := (0.4 * model.QualityRating / 10.0) +
			(0.3 * model.SpeedRating / 10.0) +
			(0.3 * costScore)

		if score > bestScore {
			bestScore = score
			bestModel = model
		}
	}

	if bestModel == nil {
		return &ModelRegistry[0], nil
	}

	r.CachedModel = bestModel
	return bestModel, nil
}

func (r *Router) filterModels(constraints SelectionConstraints) []Model {
	var filtered []Model
	for _, model := range ModelRegistry {
		if r.modelMeetsConstraints(&model, constraints) {
			filtered = append(filtered, model)
		}
	}
	return filtered
}

func (r *Router) modelMeetsConstraints(model *Model, constraints SelectionConstraints) bool {
	requiredCaps := r.getRequiredCapabilities(constraints.TaskType)
	if model.Capabilities&requiredCaps != requiredCaps {
		return false
	}
	if constraints.MaxCostPerM > 0 {
		avgCost := (model.CostPerMInput + model.CostPerMOutput) / 2.0
		if avgCost > constraints.MaxCostPerM {
			return false
		}
	}
	if constraints.MinSpeed > 0 && model.SpeedRating < constraints.MinSpeed {
		return false
	}
	if constraints.MinQuality > 0 && model.QualityRating < constraints.MinQuality {
		return false
	}
	if constraints.MinContext > 0 && model.ContextSize < constraints.MinContext {
		return false
	}
	if constraints.PreferredProvider != "" && model.Provider != constraints.PreferredProvider {
		return false
	}
	return true
}

func (r *Router) getRequiredCapabilities(taskType TaskType) Capability {
	switch taskType {
	case TASK_CHAT:
		return TEXT
	case TASK_CODE:
		return TEXT | CODE
	case TASK_VISION:
		return TEXT | VISION
	case TASK_REASONING:
		return TEXT | REASONING
	case TASK_CREATIVE:
		return TEXT | CREATIVE
	case TASK_MATH:
		return TEXT | MATH
	case TASK_SPEECH:
		return SPEECH
	case TASK_IMAGE_GEN:
		return IMAGE_GEN
	default:
		return TEXT
	}
}

func (r *Router) SetRegime(regime int) {
	if regime >= 1 && regime <= 3 {
		r.RegimeMode = regime
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// API CLIENT (OpenAI-compatible)
// ═══════════════════════════════════════════════════════════════════════════

type Message struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

type ChatRequest struct {
	Model       string    `json:"model"`
	Messages    []Message `json:"messages"`
	Temperature float64   `json:"temperature,omitempty"`
	MaxTokens   int       `json:"max_tokens,omitempty"`
	Stream      bool      `json:"stream"`
}

type ChatResponse struct {
	ID      string   `json:"id"`
	Object  string   `json:"object"`
	Created int64    `json:"created"`
	Model   string   `json:"model"`
	Choices []Choice `json:"choices"`
	Usage   Usage    `json:"usage"`
}

type Choice struct {
	Index        int            `json:"index"`
	Message      MessageContent `json:"message"`
	FinishReason string         `json:"finish_reason"`
}

type MessageContent struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

type Usage struct {
	PromptTokens     int `json:"prompt_tokens"`
	CompletionTokens int `json:"completion_tokens"`
	TotalTokens      int `json:"total_tokens"`
}

// Chat sends a chat completion request
func (r *Router) Chat(modelID string, messages []Message, temperature float64, maxTokens int) (*ChatResponse, error) {
	if !r.IsConfigured() {
		return nil, fmt.Errorf("AIML API key not configured - set AIMLAPI_KEY or OPENAI_API_KEY env var")
	}

	request := ChatRequest{
		Model:       modelID,
		Messages:    messages,
		Temperature: temperature,
		MaxTokens:   maxTokens,
		Stream:      false,
	}

	var response *ChatResponse
	var lastErr error

	for retry := 0; retry < MAX_RETRIES; retry++ {
		response, lastErr = r.callAPI(request)
		if lastErr == nil {
			break
		}
		backoff := time.Duration(math.Pow(2, float64(retry))) * time.Second
		time.Sleep(backoff)
	}

	return response, lastErr
}

func (r *Router) callAPI(request ChatRequest) (*ChatResponse, error) {
	r.RateLimiter <- struct{}{}
	go func() {
		time.Sleep(time.Minute / RATE_LIMIT)
		<-r.RateLimiter
	}()

	requestBody, err := json.Marshal(request)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	req, err := http.NewRequest("POST", r.BaseURL+"/chat/completions", bytes.NewBuffer(requestBody))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+r.APIKey)

	resp, err := r.HTTPClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to send request: %w", err)
	}
	defer resp.Body.Close()

	responseBody, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("API error (status %d): %s", resp.StatusCode, string(responseBody))
	}

	var response ChatResponse
	if err := json.Unmarshal(responseBody, &response); err != nil {
		return nil, fmt.Errorf("failed to unmarshal response: %w", err)
	}

	return &response, nil
}

// SimpleChat is a convenience wrapper for basic text chat
func (r *Router) SimpleChat(modelID string, userMessage string) (string, error) {
	messages := []Message{
		{Role: "user", Content: userMessage},
	}

	response, err := r.Chat(modelID, messages, 0.7, 2000)
	if err != nil {
		return "", err
	}

	if len(response.Choices) == 0 {
		return "", fmt.Errorf("no choices in response")
	}

	return response.Choices[0].Message.Content, nil
}

// ResearchChat sends a research-focused query with system context
func (r *Router) ResearchChat(query string, context string) (string, error) {
	model, err := r.SelectModel(SelectionConstraints{
		TaskType:    TASK_REASONING,
		MaxCostPerM: 5.0,
		MinQuality:  8.0,
	})
	if err != nil {
		model = &ModelRegistry[0]
	}

	systemPrompt := `You are an urban research assistant for IIHS (Indian Institute for Human Settlements).
Your role is to help researchers analyze urban data, census information, survey results, and spatial patterns.
Provide academically rigorous, neutral analysis. Cite methodological considerations where relevant.
Be concise but thorough. Use structured responses when analyzing data.`

	if context != "" {
		systemPrompt += "\n\nContext:\n" + context
	}

	messages := []Message{
		{Role: "system", Content: systemPrompt},
		{Role: "user", Content: query},
	}

	response, err := r.Chat(model.ID, messages, 0.3, 4000)
	if err != nil {
		return "", err
	}

	if len(response.Choices) == 0 {
		return "", fmt.Errorf("no response from model")
	}

	return response.Choices[0].Message.Content, nil
}

// ListModels returns available models
func (r *Router) ListModels() []Model {
	return ModelRegistry
}

// GetModelByID retrieves a specific model
func (r *Router) GetModelByID(id string) (*Model, error) {
	for i := range ModelRegistry {
		if ModelRegistry[i].ID == id || strings.Contains(ModelRegistry[i].ID, id) {
			return &ModelRegistry[i], nil
		}
	}
	return nil, fmt.Errorf("model not found: %s", id)
}
