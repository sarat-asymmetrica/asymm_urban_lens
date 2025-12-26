// Package aimlapi - Image generation support
package aimlapi

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
)

// ═══════════════════════════════════════════════════════════════════════════
// IMAGE GENERATION TYPES
// ═══════════════════════════════════════════════════════════════════════════

// ImageRequest represents an image generation request
type ImageRequest struct {
	Model          string `json:"model"`           // flux/dev, stable-diffusion-xl-base-1.0, etc.
	Prompt         string `json:"prompt"`          // Text description of desired image
	NegativePrompt string `json:"negative_prompt,omitempty"` // What to avoid
	N              int    `json:"n,omitempty"`     // Number of images (default: 1)
	Size           string `json:"size,omitempty"`  // e.g., "1024x1024", "512x512"
	Quality        string `json:"quality,omitempty"` // "standard" or "hd"
	Style          string `json:"style,omitempty"`   // "vivid" or "natural"
	ResponseFormat string `json:"response_format,omitempty"` // "url" or "b64_json"
}

// ImageResponse represents the API response
type ImageResponse struct {
	Created int64       `json:"created"`
	Data    []ImageData `json:"data"`
}

// ImageData represents a single generated image
type ImageData struct {
	URL           string `json:"url,omitempty"`
	B64JSON       string `json:"b64_json,omitempty"`
	RevisedPrompt string `json:"revised_prompt,omitempty"`
}

// ImageResult is a high-level result structure
type ImageResult struct {
	URL    string // URL to the generated image
	Base64 string // Base64-encoded image (if requested)
	Width  int    // Image width
	Height int    // Image height
	Prompt string // Original prompt
	Model  string // Model used for generation
}

// ═══════════════════════════════════════════════════════════════════════════
// IMAGE GENERATION EXECUTION
// ═══════════════════════════════════════════════════════════════════════════

// executeImageRequestWithRetry executes image generation with retry logic
func (c *Client) executeImageRequestWithRetry(ctx context.Context, req ImageRequest) (*ImageResponse, error) {
	var lastErr error
	maxRetries := 3

	for attempt := 0; attempt < maxRetries; attempt++ {
		// Wait for rate limiter
		if err := c.rateLimiter.Wait(ctx); err != nil {
			return nil, fmt.Errorf("rate limiter error: %w", err)
		}

		resp, err := c.executeImageRequest(ctx, req)
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

// executeImageRequest executes a single image generation request
func (c *Client) executeImageRequest(ctx context.Context, req ImageRequest) (*ImageResponse, error) {
	// Apply defaults
	if req.N == 0 {
		req.N = 1
	}
	if req.Size == "" {
		req.Size = "1024x1024"
	}
	if req.ResponseFormat == "" {
		req.ResponseFormat = "url"
	}

	// Marshal request
	reqBody, err := json.Marshal(req)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", c.baseURL+"/images/generations", bytes.NewReader(reqBody))
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
	var imageResp ImageResponse
	if err := json.Unmarshal(body, &imageResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &imageResp, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVENIENCE METHODS
// ═══════════════════════════════════════════════════════════════════════════

// GenerateImageAdvanced generates an image with full control
func (c *Client) GenerateImageAdvanced(ctx context.Context, req ImageRequest) (*ImageResult, error) {
	resp, err := c.executeImageRequestWithRetry(ctx, req)
	if err != nil {
		return nil, err
	}

	if len(resp.Data) == 0 {
		return nil, fmt.Errorf("no images generated")
	}

	// Extract dimensions from size string (e.g., "1024x1024")
	width, height := parseSizeDimensions(req.Size)

	return &ImageResult{
		URL:    resp.Data[0].URL,
		Base64: resp.Data[0].B64JSON,
		Width:  width,
		Height: height,
		Prompt: req.Prompt,
		Model:  req.Model,
	}, nil
}

// GenerateDiagramAdvanced creates a technical diagram
func (c *Client) GenerateDiagramAdvanced(ctx context.Context, description string, style string) (*ImageResult, error) {
	prompt := fmt.Sprintf("Create a clean, professional %s diagram showing: %s. Use clear labels, logical layout, and minimal colors.", style, description)

	req := ImageRequest{
		Model:  "flux/dev",
		Prompt: prompt,
		Size:   "1024x1024",
		Style:  "natural",
	}

	return c.GenerateImageAdvanced(ctx, req)
}

// GenerateChartVisualization creates data visualizations
func (c *Client) GenerateChartVisualization(ctx context.Context, dataDescription string, chartType string) (*ImageResult, error) {
	prompt := fmt.Sprintf("Create a %s chart visualization of: %s. Use professional styling with clear axes, labels, and legend.", chartType, dataDescription)

	req := ImageRequest{
		Model:  "flux/dev",
		Prompt: prompt,
		Size:   "1024x1024",
		Style:  "natural",
	}

	return c.GenerateImageAdvanced(ctx, req)
}

// GenerateMapVisualization creates map-based visualizations
func (c *Client) GenerateMapVisualization(ctx context.Context, location string, dataOverlay string) (*ImageResult, error) {
	prompt := fmt.Sprintf("Create a map visualization of %s showing %s. Use clear geographic features, appropriate color coding, and informative legend.", location, dataOverlay)

	req := ImageRequest{
		Model:  "flux/dev",
		Prompt: prompt,
		Size:   "1024x1024",
		Style:  "natural",
	}

	return c.GenerateImageAdvanced(ctx, req)
}

// GenerateInfographic creates infographic-style visuals
func (c *Client) GenerateInfographic(ctx context.Context, topic string, keyPoints []string) (*ImageResult, error) {
	points := ""
	for i, point := range keyPoints {
		points += fmt.Sprintf("%d. %s ", i+1, point)
	}

	prompt := fmt.Sprintf("Create a modern infographic about %s. Include these key points: %s. Use icons, clear hierarchy, and professional color scheme.", topic, points)

	req := ImageRequest{
		Model:  "flux/dev",
		Prompt: prompt,
		Size:   "1024x1024",
		Style:  "vivid",
	}

	return c.GenerateImageAdvanced(ctx, req)
}

// GenerateBatchImages generates multiple images from different prompts
func (c *Client) GenerateBatchImages(ctx context.Context, prompts []string, model string) ([]*ImageResult, error) {
	if model == "" {
		model = "flux/dev"
	}

	results := make([]*ImageResult, len(prompts))
	errors := make([]error, len(prompts))

	// Sequential generation (avoid overwhelming API)
	for i, prompt := range prompts {
		req := ImageRequest{
			Model:  model,
			Prompt: prompt,
			Size:   "1024x1024",
		}

		result, err := c.GenerateImageAdvanced(ctx, req)
		if err != nil {
			errors[i] = err
		} else {
			results[i] = result
		}
	}

	// Check if all failed
	allFailed := true
	for _, err := range errors {
		if err == nil {
			allFailed = false
			break
		}
	}

	if allFailed {
		return nil, fmt.Errorf("all image generations failed: %v", errors[0])
	}

	return results, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// parseSizeDimensions parses "1024x1024" into width and height
func parseSizeDimensions(size string) (int, int) {
	// Common sizes
	switch size {
	case "256x256":
		return 256, 256
	case "512x512":
		return 512, 512
	case "1024x1024":
		return 1024, 1024
	case "1792x1024":
		return 1792, 1024
	case "1024x1792":
		return 1024, 1792
	default:
		return 1024, 1024 // Default
	}
}
