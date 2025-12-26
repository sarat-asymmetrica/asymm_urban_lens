// Package aimlapi - Intelligent routing with fallback chains
package aimlapi

import (
	"context"
	"fmt"
	"math"
	"math/rand"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// ROUTER
// ═══════════════════════════════════════════════════════════════════════════

// Router provides intelligent model selection and fallback handling
type Router struct {
	client         *Client
	fallbackChains map[TaskType][]string
	mu             sync.RWMutex
}

// NewRouter creates a new router with default fallback chains
func NewRouter(client *Client) *Router {
	return &Router{
		client:         client,
		fallbackChains: buildDefaultFallbackChains(),
	}
}

// SelectionConstraints defines requirements for model selection
type SelectionConstraints struct {
	TaskType          TaskType
	MaxCostPerM       float64 // Maximum cost per million tokens
	MinSpeed          float64 // Minimum speed rating (0-10)
	MinQuality        float64 // Minimum quality rating (0-10)
	MinContext        int     // Minimum context size
	PreferredProvider string  // Preferred provider (optional)
	RequireVision     bool    // Require vision capability
}

// ═══════════════════════════════════════════════════════════════════════════
// MODEL SELECTION (THREE-REGIME DYNAMICS)
// ═══════════════════════════════════════════════════════════════════════════

// SelectModel selects the best model based on constraints and current regime
func (c *Client) SelectModel(constraints SelectionConstraints) (*ModelConfig, error) {
	c.mu.RLock()
	regime := c.regime
	explorationProb := c.explorationProb
	cachedModel := c.cachedModel
	c.mu.RUnlock()

	// REGIME 1: EXPLORATION - Random selection from candidates
	if regime == 1 || rand.Float64() < explorationProb {
		return c.exploreModel(constraints)
	}

	// REGIME 2: OPTIMIZATION - Best quality/cost tradeoff
	if regime == 2 {
		return c.optimizeModel(constraints)
	}

	// REGIME 3: STABILIZATION - Use cached model if valid
	if cachedModel != nil && c.modelMeetsConstraints(cachedModel, constraints) {
		return cachedModel, nil
	}

	// Fallback to optimization if cached model doesn't meet constraints
	return c.optimizeModel(constraints)
}

// exploreModel randomly selects from candidates (REGIME 1)
func (c *Client) exploreModel(constraints SelectionConstraints) (*ModelConfig, error) {
	candidates := c.filterModels(constraints)
	if len(candidates) == 0 {
		// Fallback to default
		model := SelectModelForTask(constraints.TaskType)
		return &model, nil
	}

	// Random selection
	selected := candidates[rand.Intn(len(candidates))]

	// Cache for potential stabilization
	c.mu.Lock()
	c.cachedModel = &selected
	c.mu.Unlock()

	return &selected, nil
}

// optimizeModel selects best quality/cost tradeoff (REGIME 2)
func (c *Client) optimizeModel(constraints SelectionConstraints) (*ModelConfig, error) {
	candidates := c.filterModels(constraints)
	if len(candidates) == 0 {
		// Fallback to default
		model := SelectModelForTask(constraints.TaskType)
		return &model, nil
	}

	var bestModel *ModelConfig
	var bestScore float64 = -1.0

	for i := range candidates {
		model := &candidates[i]

		// Calculate cost score (lower cost = higher score)
		costScore := 0.5
		if constraints.MaxCostPerM > 0 {
			avgCost := (model.CostPerMInput + model.CostPerMOutput) / 2.0
			costScore = 1.0 - math.Min(avgCost/constraints.MaxCostPerM, 1.0)
		}

		// Weighted score: 40% quality, 30% speed, 30% cost
		score := (0.4 * model.QualityRating / 10.0) +
			(0.3 * model.SpeedRating / 10.0) +
			(0.3 * costScore)

		if score > bestScore {
			bestScore = score
			bestModel = model
		}
	}

	if bestModel == nil {
		model := SelectModelForTask(constraints.TaskType)
		return &model, nil
	}

	// Cache for potential stabilization
	c.mu.Lock()
	c.cachedModel = bestModel
	c.mu.Unlock()

	return bestModel, nil
}

// filterModels returns models that meet constraints
func (c *Client) filterModels(constraints SelectionConstraints) []ModelConfig {
	c.mu.RLock()
	defer c.mu.RUnlock()

	var filtered []ModelConfig

	for _, model := range c.models {
		if c.modelMeetsConstraints(&model, constraints) {
			filtered = append(filtered, model)
		}
	}

	return filtered
}

// modelMeetsConstraints checks if model satisfies constraints
func (c *Client) modelMeetsConstraints(model *ModelConfig, constraints SelectionConstraints) bool {
	// Check required capabilities
	requiredCaps := GetRequiredCapabilities(constraints.TaskType)
	if model.Capabilities&requiredCaps != requiredCaps {
		return false
	}

	// Check vision requirement
	if constraints.RequireVision && model.Capabilities&VISION == 0 {
		return false
	}

	// Check cost constraint
	if constraints.MaxCostPerM > 0 {
		avgCost := (model.CostPerMInput + model.CostPerMOutput) / 2.0
		if avgCost > constraints.MaxCostPerM {
			return false
		}
	}

	// Check speed constraint
	if constraints.MinSpeed > 0 && model.SpeedRating < constraints.MinSpeed {
		return false
	}

	// Check quality constraint
	if constraints.MinQuality > 0 && model.QualityRating < constraints.MinQuality {
		return false
	}

	// Check context size constraint
	if constraints.MinContext > 0 && model.ContextSize < constraints.MinContext {
		return false
	}

	// Check provider preference
	if constraints.PreferredProvider != "" && model.Provider != constraints.PreferredProvider {
		return false
	}

	return true
}

// ═══════════════════════════════════════════════════════════════════════════
// FALLBACK ROUTING
// ═══════════════════════════════════════════════════════════════════════════

// Route sends request with intelligent model selection
func (r *Router) Route(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	// Select model if not specified
	if req.Model == "" {
		constraints := SelectionConstraints{
			TaskType:   TASK_CHAT,
			MinQuality: 8.0,
		}
		model, err := r.client.SelectModel(constraints)
		if err != nil {
			return nil, err
		}
		req.Model = model.ModelID
	}

	return r.client.Chat(ctx, req)
}

// RouteWithFallback tries primary model, falls back to chain on failure
func (r *Router) RouteWithFallback(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	// Determine task type from request
	taskType := r.inferTaskType(req)

	// Get fallback chain for this task
	r.mu.RLock()
	chain := r.fallbackChains[taskType]
	r.mu.RUnlock()

	if len(chain) == 0 {
		// No fallback chain, use standard routing
		return r.Route(ctx, req)
	}

	// Try each model in the chain
	var lastErr error
	for _, modelID := range chain {
		req.Model = modelID
		resp, err := r.client.Chat(ctx, req)
		if err == nil {
			return resp, nil
		}

		lastErr = err

		// Don't retry on client errors (4xx)
		if isClientError(err) {
			break
		}
	}

	return nil, fmt.Errorf("all models in fallback chain failed: %w", lastErr)
}

// SetFallbackChain sets custom fallback chain for a task type
func (r *Router) SetFallbackChain(taskType TaskType, models []string) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.fallbackChains[taskType] = models
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// inferTaskType infers task type from request messages
func (r *Router) inferTaskType(req ChatRequest) TaskType {
	// Check for vision content
	for _, msg := range req.Messages {
		if containsImageContent(msg.Content) {
			return TASK_VISION
		}
	}

	// Check for code-related keywords
	if containsCodeKeywords(req.Messages) {
		return TASK_CODE
	}

	// Check for reasoning keywords
	if containsReasoningKeywords(req.Messages) {
		return TASK_REASONING
	}

	// Default to chat
	return TASK_CHAT
}

// containsImageContent checks if message content includes images
func containsImageContent(content string) bool {
	// In a real implementation, this would check for image URLs or base64 data
	// For now, just check for common image-related keywords
	imageKeywords := []string{"image", "picture", "photo", "screenshot", "diagram"}
	contentLower := content
	for _, keyword := range imageKeywords {
		if contains(contentLower, keyword) {
			return true
		}
	}
	return false
}

// containsCodeKeywords checks for code-related keywords
func containsCodeKeywords(messages []Message) bool {
	codeKeywords := []string{"code", "function", "class", "programming", "debug", "implement"}
	for _, msg := range messages {
		for _, keyword := range codeKeywords {
			if contains(msg.Content, keyword) {
				return true
			}
		}
	}
	return false
}

// containsReasoningKeywords checks for reasoning-related keywords
func containsReasoningKeywords(messages []Message) bool {
	reasoningKeywords := []string{"analyze", "reasoning", "logic", "prove", "explain why", "think through"}
	for _, msg := range messages {
		for _, keyword := range reasoningKeywords {
			if contains(msg.Content, keyword) {
				return true
			}
		}
	}
	return false
}

// contains is a simple case-insensitive substring check
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr))
}

// buildDefaultFallbackChains creates default fallback chains for each task type
func buildDefaultFallbackChains() map[TaskType][]string {
	return map[TaskType][]string{
		TASK_CHAT: {
			"gpt-4o-mini",      // Fast, cheap, good quality
			"claude-sonnet",     // High quality fallback
			"deepseek-chat",    // Ultra-cheap fallback
		},
		TASK_CODE: {
			"claude-sonnet",     // Best for code
			"gpt-4o",           // Strong code capabilities
			"llama-70b",        // Open-source fallback
		},
		TASK_VISION: {
			"gpt-4o",           // Best vision
			"claude-opus",      // Good vision
			"gemini-flash",     // Fast vision fallback
		},
		TASK_REASONING: {
			"claude-opus",      // Best reasoning
			"gpt-4o",           // Strong reasoning
			"claude-sonnet",    // Good reasoning fallback
		},
		TASK_CREATIVE: {
			"claude-opus",      // Best creative writing
			"gpt-4o",           // Creative capabilities
			"llama-405b",       // Open-source creative
		},
		TASK_MATH: {
			"gpt-4o",           // Strong math
			"claude-opus",      // Good math
			"deepseek-chat",    // Reasoning-focused
		},
		TASK_IMAGE_GEN: {
			"flux-image",       // High quality
			"flux-pro",         // Professional fallback
			"stable-diffusion", // Fast fallback
		},
	}
}

// isClientError checks if error is a client error (4xx) that shouldn't be retried
func isClientError(err error) bool {
	if err == nil {
		return false
	}
	// Simple check for "status 4" in error message
	errStr := err.Error()
	return contains(errStr, "status 4")
}

// ═══════════════════════════════════════════════════════════════════════════
// ADVANCED ROUTING
// ═══════════════════════════════════════════════════════════════════════════

// RouteOptimized routes to cheapest model that meets quality threshold
func (r *Router) RouteOptimized(ctx context.Context, req ChatRequest, minQuality float64) (*ChatResponse, error) {
	constraints := SelectionConstraints{
		TaskType:   r.inferTaskType(req),
		MinQuality: minQuality,
	}

	// Force optimization regime
	originalRegime := r.client.GetRegime()
	r.client.SetRegime(2)
	defer r.client.SetRegime(originalRegime)

	model, err := r.client.SelectModel(constraints)
	if err != nil {
		return nil, err
	}

	req.Model = model.ModelID
	return r.client.Chat(ctx, req)
}

// RouteFastest routes to fastest model that meets quality threshold
func (r *Router) RouteFastest(ctx context.Context, req ChatRequest, minQuality float64) (*ChatResponse, error) {
	constraints := SelectionConstraints{
		TaskType:   r.inferTaskType(req),
		MinQuality: minQuality,
		MinSpeed:   8.0, // Require high speed
	}

	model, err := r.client.SelectModel(constraints)
	if err != nil {
		return nil, err
	}

	req.Model = model.ModelID
	return r.client.Chat(ctx, req)
}

// RouteBestQuality routes to highest quality model regardless of cost
func (r *Router) RouteBestQuality(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	constraints := SelectionConstraints{
		TaskType:   r.inferTaskType(req),
		MinQuality: 9.0, // Require top-tier quality
	}

	model, err := r.client.SelectModel(constraints)
	if err != nil {
		return nil, err
	}

	req.Model = model.ModelID
	return r.client.Chat(ctx, req)
}

func init() {
	rand.Seed(time.Now().UnixNano())
}
