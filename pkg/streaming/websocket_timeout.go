// Package streaming - Timeout wrappers for WebSocket operations
package streaming

import (
	"context"
	"encoding/json"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/resilience"
)

// WebSocketMessage wraps WebSocket read result
type WebSocketMessage struct {
	MessageType int
	Data        []byte
}

// writeJSONWithTimeout writes JSON to WebSocket with 10s timeout
func (c *Client) writeJSONWithTimeout(ctx context.Context, v interface{}) error {
	return resilience.WithWebSocketTimeout(ctx, func() error {
		c.mu.Lock()
		defer c.mu.Unlock()
		return c.Conn.WriteJSON(v)
	})
}

// readMessageWithTimeout reads from WebSocket with 10s timeout
func (c *Client) readMessageWithTimeout(ctx context.Context) (*WebSocketMessage, error) {
	return resilience.WithWebSocketTimeoutResult(ctx, func() (*WebSocketMessage, error) {
		// Set read deadline
		c.Conn.SetReadDeadline(time.Now().Add(resilience.DefaultWebSocketTimeout))
		defer c.Conn.SetReadDeadline(time.Time{}) // Clear deadline

		msgType, data, err := c.Conn.ReadMessage()
		if err != nil {
			return nil, err
		}
		return &WebSocketMessage{MessageType: msgType, Data: data}, nil
	})
}

// ReadPumpWithTimeout reads messages with timeout protection
// This should replace the current ReadPump method
func (c *Client) ReadPumpWithTimeout(ctx context.Context) {
	defer func() {
		c.Hub.Unregister <- c
		c.Conn.Close()
	}()

	for {
		// Read with timeout
		msg, err := c.readMessageWithTimeout(ctx)
		if err != nil {
			// Check if it's a timeout
			if err == resilience.ErrTimeout {
				// Log timeout but continue (WebSocket might be idle)
				continue
			}
			// Other errors - break
			break
		}

		// Handle incoming message - support both "type" (frontend) and "action" (legacy)
		var request struct {
			Type   string `json:"type"`
			Action string `json:"action"`
			Input  string `json:"input"`
		}

		if err := json.Unmarshal(msg.Data, &request); err == nil {
			// Use "type" if provided, fall back to "action"
			action := request.Type
			if action == "" {
				action = request.Action
			}
			// Map "query" to "analyze" for frontend compatibility
			if action == "query" {
				action = "analyze"
			}
			c.Hub.HandleRequest(c, action, request.Input)
		}
	}
}

// WritePumpWithTimeout pumps messages with timeout protection
// This should replace the current WritePump method
func (c *Client) WritePumpWithTimeout(ctx context.Context) {
	defer func() {
		c.Conn.Close()
	}()

	for msg := range c.Send {
		// Write with timeout
		err := c.writeJSONWithTimeout(ctx, msg)
		if err != nil {
			// Log error and exit
			return
		}
	}
}
