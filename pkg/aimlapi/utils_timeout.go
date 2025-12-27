// Package aimlapi - Timeout-wrapped HTTP execution
// Extends utils.go with resilience package integration
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

// executeChatRequestWithTimeout executes a single chat request with 30s timeout
func (c *Client) executeChatRequestWithTimeout(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	// Execute with timeout (30 seconds default for API calls)
	return resilience.WithAPITimeoutResult(ctx, func() (*ChatResponse, error) {
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
	})
}
