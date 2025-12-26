// Package api provides WebSocket streaming for real-time conversation
package api

import (
	"context"
	"encoding/json"
	"log"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/conversation"
	"github.com/gorilla/websocket"
)

// ═══════════════════════════════════════════════════════════════════════════
// WEBSOCKET MESSAGE TYPES
// ═══════════════════════════════════════════════════════════════════════════

// WSMessageType identifies the type of WebSocket message
type WSMessageType string

const (
	WSToken         WSMessageType = "token"          // Streaming token
	WSPhaseChange   WSMessageType = "phase_change"   // Phase transition
	WSEntity        WSMessageType = "entity"         // Entity detected
	WSDiscovery     WSMessageType = "discovery"      // Discovery made
	WSImage         WSMessageType = "image"          // Visualization ready
	WSComplete      WSMessageType = "complete"       // Response complete
	WSError         WSMessageType = "error"          // Error occurred
	WSWelcome       WSMessageType = "welcome"        // Connection established
	WSStateChange   WSMessageType = "state_change"   // Conversation state changed
	WSInsight       WSMessageType = "insight"        // Insight discovered
	WSWhyStep       WSMessageType = "why_step"       // Why-chain step
)

// WSMessage represents a WebSocket message
type WSMessage struct {
	Type      WSMessageType          `json:"type"`
	Content   string                 `json:"content,omitempty"`
	Data      map[string]interface{} `json:"data,omitempty"`
	Timestamp time.Time              `json:"timestamp"`
}

// WSClient represents a WebSocket client connection
type WSClient struct {
	Conn   *websocket.Conn
	Send   chan WSMessage
	Server *Server
}

// ═══════════════════════════════════════════════════════════════════════════
// CLIENT METHODS
// ═══════════════════════════════════════════════════════════════════════════

// WritePump pumps messages to the WebSocket connection
func (c *WSClient) WritePump() {
	ticker := time.NewTicker(54 * time.Second) // Ping interval
	defer func() {
		ticker.Stop()
		c.Conn.Close()
	}()

	for {
		select {
		case message, ok := <-c.Send:
			c.Conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
			if !ok {
				// Channel closed
				c.Conn.WriteMessage(websocket.CloseMessage, []byte{})
				return
			}

			if err := c.Conn.WriteJSON(message); err != nil {
				log.Printf("WebSocket write error: %v", err)
				return
			}

		case <-ticker.C:
			c.Conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
			if err := c.Conn.WriteMessage(websocket.PingMessage, nil); err != nil {
				return
			}
		}
	}
}

// ReadPump reads messages from the WebSocket connection
func (c *WSClient) ReadPump() {
	defer func() {
		c.Conn.Close()
	}()

	c.Conn.SetReadDeadline(time.Now().Add(60 * time.Second))
	c.Conn.SetPongHandler(func(string) error {
		c.Conn.SetReadDeadline(time.Now().Add(60 * time.Second))
		return nil
	})

	// Send welcome message
	c.Send <- WSMessage{
		Type:      WSWelcome,
		Content:   "Connected to ASYA",
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"version": "0.1.0",
			"ready":   true,
		},
	}

	for {
		_, message, err := c.Conn.ReadMessage()
		if err != nil {
			if websocket.IsUnexpectedCloseError(err, websocket.CloseGoingAway, websocket.CloseAbnormalClosure) {
				log.Printf("WebSocket error: %v", err)
			}
			break
		}

		c.handleMessage(message)
	}
}

// handleMessage processes incoming WebSocket messages
func (c *WSClient) handleMessage(message []byte) {
	var request struct {
		Action    string `json:"action"`    // "create_session", "send_message", "request_hint"
		SessionID string `json:"session_id,omitempty"`
		UserID    string `json:"user_id,omitempty"`
		Message   string `json:"message,omitempty"`
	}

	if err := json.Unmarshal(message, &request); err != nil {
		c.Send <- WSMessage{
			Type:      WSError,
			Content:   "Invalid message format",
			Timestamp: time.Now(),
		}
		return
	}

	switch request.Action {
	case "create_session":
		c.handleCreateSession(request.UserID)

	case "send_message":
		c.handleSendMessage(request.SessionID, request.Message)

	case "request_hint":
		c.handleRequestHint(request.SessionID)

	default:
		c.Send <- WSMessage{
			Type:      WSError,
			Content:   "Unknown action: " + request.Action,
			Timestamp: time.Now(),
		}
	}
}

// handleCreateSession creates a new conversation session
func (c *WSClient) handleCreateSession(userID string) {
	conv := c.Server.CreateSession(userID)

	c.Send <- WSMessage{
		Type:      WSStateChange,
		Content:   "Session created",
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"session_id": conv.ID,
			"state":      conv.State,
			"phase":      conv.Phase,
		},
	}
}

// handleSendMessage processes a user message with streaming
func (c *WSClient) handleSendMessage(sessionID, userMessage string) {
	conv, exists := c.Server.GetSession(sessionID)
	if !exists {
		c.Send <- WSMessage{
			Type:      WSError,
			Content:   "Session not found",
			Timestamp: time.Now(),
		}
		return
	}

	// Create streaming context
	ctx := NewStreamingContext(c, conv)

	// Process message with streaming
	response, err := c.Server.ProcessMessage(ctx.Context, conv, userMessage)
	if err != nil {
		c.Send <- WSMessage{
			Type:      WSError,
			Content:   err.Error(),
			Timestamp: time.Now(),
		}
		return
	}

	// Stream response tokens
	c.streamTokens(response)

	// Send completion
	c.Send <- WSMessage{
		Type:      WSComplete,
		Content:   response,
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"state":          conv.State,
			"phase":          conv.Phase,
			"message_count":  len(conv.Messages),
			"why_depth":      conv.WhyChainDepth,
			"insights_count": len(conv.Insights),
		},
	}
}

// handleRequestHint provides a contextual hint
func (c *WSClient) handleRequestHint(sessionID string) {
	conv, exists := c.Server.GetSession(sessionID)
	if !exists {
		c.Send <- WSMessage{
			Type:      WSError,
			Content:   "Session not found",
			Timestamp: time.Now(),
		}
		return
	}

	hint := c.generateHint(conv)

	c.Send <- WSMessage{
		Type:      WSDiscovery,
		Content:   hint,
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"type":  "hint",
			"state": conv.State,
			"phase": conv.Phase,
		},
	}
}

// streamTokens simulates streaming response (TODO: integrate with real LLM streaming)
func (c *WSClient) streamTokens(text string) {
	words := splitIntoWords(text)
	for i, word := range words {
		c.Send <- WSMessage{
			Type:      WSToken,
			Content:   word + " ",
			Timestamp: time.Now(),
			Data: map[string]interface{}{
				"index": i,
				"total": len(words),
			},
		}
		time.Sleep(50 * time.Millisecond) // Simulate streaming delay
	}
}

// generateHint creates a contextual hint based on conversation state
func (c *WSClient) generateHint(conv *conversation.Conversation) string {
	switch conv.State {
	case conversation.StateGreeting:
		return "Try describing something you've observed recently. What caught your attention?"

	case conversation.StateAnchoring:
		return "Focus on what you can see, hear, or feel. Be specific about the sensory details."

	case conversation.StateWhyChaining:
		return "Think about what causes that to happen. What's the underlying reason?"

	case conversation.StateSynthesizing:
		return "How might this connect to other things you know? What's similar in other areas?"

	case conversation.StateFormalizing:
		return "You're close to a breakthrough! Can you state your discovery as a clear principle?"

	case conversation.StateCelebrating:
		return "You did it! Want to explore another observation?"

	default:
		return "Keep exploring. Your curiosity is leading you somewhere interesting!"
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// STREAMING CONTEXT
// ═══════════════════════════════════════════════════════════════════════════

// StreamingContext provides context for streaming responses
type StreamingContext struct {
	Context      context.Context
	Client       *WSClient
	Conversation *conversation.Conversation
}

// NewStreamingContext creates a new streaming context
func NewStreamingContext(client *WSClient, conv *conversation.Conversation) *StreamingContext {
	return &StreamingContext{
		Context:      context.Background(),
		Client:       client,
		Conversation: conv,
	}
}

// EmitPhaseChange emits a phase change event
func (sc *StreamingContext) EmitPhaseChange(phase conversation.VoidFlowPhase) {
	sc.Client.Send <- WSMessage{
		Type:      WSPhaseChange,
		Content:   string(phase),
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"phase":      phase,
			"session_id": sc.Conversation.ID,
		},
	}
}

// EmitStateChange emits a state change event
func (sc *StreamingContext) EmitStateChange(state conversation.ConversationState) {
	sc.Client.Send <- WSMessage{
		Type:      WSStateChange,
		Content:   string(state),
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"state":      state,
			"session_id": sc.Conversation.ID,
		},
	}
}

// EmitEntity emits an entity detection event
func (sc *StreamingContext) EmitEntity(entity conversation.Entity) {
	sc.Client.Send <- WSMessage{
		Type:      WSEntity,
		Content:   entity.Name,
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"entity_type": entity.Type,
			"attributes":  entity.Attributes,
		},
	}
}

// EmitInsight emits an insight discovery event
func (sc *StreamingContext) EmitInsight(insight conversation.Insight) {
	sc.Client.Send <- WSMessage{
		Type:      WSInsight,
		Content:   insight.Description,
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"domain":      insight.Domain,
			"connections": insight.Connections,
			"why_depth":   insight.WhyDepth,
		},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func splitIntoWords(text string) []string {
	// Simple word splitting (can be enhanced)
	words := []string{}
	current := ""
	for _, char := range text {
		if char == ' ' || char == '\n' {
			if current != "" {
				words = append(words, current)
				current = ""
			}
		} else {
			current += string(char)
		}
	}
	if current != "" {
		words = append(words, current)
	}
	return words
}
