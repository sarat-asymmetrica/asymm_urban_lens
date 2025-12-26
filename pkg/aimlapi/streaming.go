// Package aimlapi - Streaming support for real-time chat
package aimlapi

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// STREAMING TYPES
// ═══════════════════════════════════════════════════════════════════════════

// StreamChunk represents a chunk of streamed content
type StreamChunk struct {
	Content    string // The actual text content
	Done       bool   // Whether streaming is complete
	Error      error  // Error if any occurred
	TokenCount int    // Number of tokens in this chunk
	Model      string // Model that generated this chunk
}

// StreamDelta represents a delta in SSE format
type StreamDelta struct {
	ID      string `json:"id"`
	Object  string `json:"object"`
	Created int64  `json:"created"`
	Model   string `json:"model"`
	Choices []struct {
		Index int `json:"index"`
		Delta struct {
			Role    string `json:"role,omitempty"`
			Content string `json:"content,omitempty"`
		} `json:"delta"`
		FinishReason *string `json:"finish_reason"`
	} `json:"choices"`
}

// ═══════════════════════════════════════════════════════════════════════════
// STREAMING EXECUTION
// ═══════════════════════════════════════════════════════════════════════════

// executeStreamingRequest executes a streaming chat request
func (c *Client) executeStreamingRequest(ctx context.Context, req ChatRequest) (<-chan StreamChunk, error) {
	// Wait for rate limiter
	if err := c.rateLimiter.Wait(ctx); err != nil {
		return nil, fmt.Errorf("rate limiter error: %w", err)
	}

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
	httpReq.Header.Set("Accept", "text/event-stream")

	// Send request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		defer resp.Body.Close()
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Create channel for streaming chunks
	chunks := make(chan StreamChunk, 10)

	// Start goroutine to read SSE stream
	go c.readSSEStream(resp.Body, chunks, req.Model)

	return chunks, nil
}

// readSSEStream reads Server-Sent Events stream and sends chunks to channel
func (c *Client) readSSEStream(body io.ReadCloser, chunks chan<- StreamChunk, model string) {
	defer close(chunks)
	defer body.Close()

	scanner := bufio.NewScanner(body)
	var buffer strings.Builder

	for scanner.Scan() {
		line := scanner.Text()

		// Skip empty lines and comments
		if line == "" || strings.HasPrefix(line, ":") {
			continue
		}

		// Parse SSE data line
		if strings.HasPrefix(line, "data: ") {
			data := strings.TrimPrefix(line, "data: ")

			// Check for end of stream
			if data == "[DONE]" {
				chunks <- StreamChunk{
					Content: buffer.String(),
					Done:    true,
					Model:   model,
				}
				return
			}

			// Parse JSON delta
			var delta StreamDelta
			if err := json.Unmarshal([]byte(data), &delta); err != nil {
				chunks <- StreamChunk{
					Error: fmt.Errorf("failed to parse delta: %w", err),
					Done:  true,
				}
				return
			}

			// Extract content from delta
			if len(delta.Choices) > 0 {
				content := delta.Choices[0].Delta.Content
				if content != "" {
					buffer.WriteString(content)
					chunks <- StreamChunk{
						Content:    content,
						Done:       false,
						TokenCount: len(strings.Fields(content)), // Rough token estimate
						Model:      delta.Model,
					}
				}

				// Check if streaming is complete
				if delta.Choices[0].FinishReason != nil {
					chunks <- StreamChunk{
						Content: buffer.String(),
						Done:    true,
						Model:   delta.Model,
					}
					return
				}
			}
		}
	}

	// Check for scanner errors
	if err := scanner.Err(); err != nil {
		chunks <- StreamChunk{
			Error: fmt.Errorf("stream read error: %w", err),
			Done:  true,
		}
	}
}

// StreamChat is a convenience wrapper that calls a callback for each chunk
func (c *Client) StreamChat(ctx context.Context, req ChatRequest, callback func(StreamChunk)) error {
	chunks, err := c.ChatStream(ctx, req)
	if err != nil {
		return err
	}

	for chunk := range chunks {
		if chunk.Error != nil {
			return chunk.Error
		}
		callback(chunk)
	}

	return nil
}

// StreamChatToString collects all chunks into a single string
func (c *Client) StreamChatToString(ctx context.Context, req ChatRequest) (string, error) {
	chunks, err := c.ChatStream(ctx, req)
	if err != nil {
		return "", err
	}

	var result strings.Builder
	for chunk := range chunks {
		if chunk.Error != nil {
			return "", chunk.Error
		}
		if !chunk.Done {
			result.WriteString(chunk.Content)
		}
	}

	return result.String(), nil
}

// ═══════════════════════════════════════════════════════════════════════════
// STREAMING HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// SimpleStreamChat streams a simple user message
func (c *Client) SimpleStreamChat(ctx context.Context, userMessage string, callback func(StreamChunk)) error {
	req := ChatRequest{
		Messages: []Message{
			{Role: "user", Content: userMessage},
		},
	}

	return c.StreamChat(ctx, req, callback)
}

// SystemStreamChat streams with system prompt
func (c *Client) SystemStreamChat(ctx context.Context, systemPrompt, userMessage string, callback func(StreamChunk)) error {
	req := ChatRequest{
		Messages: []Message{
			{Role: "system", Content: systemPrompt},
			{Role: "user", Content: userMessage},
		},
	}

	return c.StreamChat(ctx, req, callback)
}
