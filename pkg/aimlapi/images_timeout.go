// Package aimlapi - Timeout-wrapped image generation
// Extends images.go with resilience package integration
package aimlapi

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"

	"github.com/asymmetrica/urbanlens/pkg/resilience"
)

// executeImageRequestWithTimeout executes a single image generation request with 30s timeout
func (c *Client) executeImageRequestWithTimeout(ctx context.Context, req ImageRequest) (*ImageResponse, error) {
	// Execute with timeout (30 seconds for API calls)
	return resilience.WithAPITimeoutResult(ctx, func() (*ImageResponse, error) {
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
	})
}
