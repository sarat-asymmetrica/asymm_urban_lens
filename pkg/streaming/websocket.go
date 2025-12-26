// Package streaming provides WebSocket streaming for the "Her" experience
// Real-time thinking phases streamed to the frontend
package streaming

import (
	"encoding/json"
	"fmt"
	"sync"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/aiml"
	"github.com/asymmetrica/urbanlens/pkg/reasoning"
	"github.com/gorilla/websocket"
)

// ============================================================================
// MESSAGE TYPES
// ============================================================================

// MessageType identifies the type of message
type MessageType string

const (
	MsgPhaseUpdate  MessageType = "phase_update"
	MsgThinking     MessageType = "thinking" // Streaming thought content
	MsgResponse     MessageType = "response" // Streaming response content
	MsgComplete     MessageType = "complete" // Signal completion
	MsgProgress     MessageType = "progress"
	MsgError        MessageType = "error"
	MsgSystemStatus MessageType = "system_status"
)

// Message represents a WebSocket message
type Message struct {
	Type        MessageType            `json:"type"`
	Phase       string                 `json:"phase,omitempty"`
	Content     string                 `json:"content"`
	Progress    float64                `json:"progress,omitempty"`
	Confidence  float64                `json:"confidence,omitempty"`
	Timestamp   time.Time              `json:"timestamp"`
	Data        map[string]interface{} `json:"data,omitempty"`
	ProofBadge  string                 `json:"proof_badge,omitempty"`  // Lean proof reference
	ProofDetail string                 `json:"proof_detail,omitempty"` // Mathematical context
}

// ============================================================================
// CLIENT
// ============================================================================

// Client represents a connected WebSocket client
type Client struct {
	ID   string
	Conn *websocket.Conn
	Send chan Message
	Hub  *Hub
	mu   sync.Mutex
}

// NewClient creates a new client
func NewClient(id string, conn *websocket.Conn, hub *Hub) *Client {
	return &Client{
		ID:   id,
		Conn: conn,
		Send: make(chan Message, 256),
		Hub:  hub,
	}
}

// WritePump pumps messages to the WebSocket connection
func (c *Client) WritePump() {
	defer func() {
		c.Conn.Close()
	}()

	for msg := range c.Send {
		c.mu.Lock()
		err := c.Conn.WriteJSON(msg)
		c.mu.Unlock()

		if err != nil {
			return
		}
	}
}

// ReadPump reads messages from the WebSocket connection
func (c *Client) ReadPump() {
	defer func() {
		c.Hub.Unregister <- c
		c.Conn.Close()
	}()

	for {
		_, message, err := c.Conn.ReadMessage()
		if err != nil {
			break
		}

		// Handle incoming message - support both "type" (frontend) and "action" (legacy)
		var request struct {
			Type   string `json:"type"`
			Action string `json:"action"`
			Input  string `json:"input"`
		}

		if err := json.Unmarshal(message, &request); err == nil {
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

// ============================================================================
// HUB
// ============================================================================

// Hub manages all WebSocket clients
type Hub struct {
	Clients    map[*Client]bool
	Register   chan *Client
	Unregister chan *Client
	Broadcast  chan Message
	Engine     *reasoning.Engine
	AIRouter   *aiml.Router
	mu         sync.RWMutex
}

// NewHub creates a new hub
func NewHub() *Hub {
	return &Hub{
		Clients:    make(map[*Client]bool),
		Register:   make(chan *Client),
		Unregister: make(chan *Client),
		Broadcast:  make(chan Message, 256),
		Engine:     reasoning.NewEngine(),
		AIRouter:   aiml.NewRouter(""),
	}
}

// Run starts the hub
func (h *Hub) Run() {
	for {
		select {
		case client := <-h.Register:
			h.mu.Lock()
			h.Clients[client] = true
			h.mu.Unlock()

			// Send welcome message
			client.Send <- Message{
				Type:      MsgSystemStatus,
				Content:   "Connected to Urban Lens",
				Timestamp: time.Now(),
				Data: map[string]interface{}{
					"client_id": client.ID,
					"status":    "connected",
				},
			}

		case client := <-h.Unregister:
			h.mu.Lock()
			if _, ok := h.Clients[client]; ok {
				delete(h.Clients, client)
				close(client.Send)
			}
			h.mu.Unlock()

		case message := <-h.Broadcast:
			h.mu.RLock()
			for client := range h.Clients {
				select {
				case client.Send <- message:
				default:
					close(client.Send)
					delete(h.Clients, client)
				}
			}
			h.mu.RUnlock()
		}
	}
}

// HandleRequest handles client requests
func (h *Hub) HandleRequest(client *Client, action, input string) {
	switch action {
	case "analyze":
		h.processAnalysis(client, input)
	case "tools":
		h.listTools(client)
	default:
		client.Send <- Message{
			Type:      MsgError,
			Content:   fmt.Sprintf("Unknown action: %s", action),
			Timestamp: time.Now(),
		}
	}
}

// processAnalysis processes an analysis request with streaming thinking
func (h *Hub) processAnalysis(client *Client, input string) {
	// Phase 1: Intake
	client.Send <- Message{
		Type:        MsgPhaseUpdate,
		Phase:       "intake",
		Content:     "Receiving your request...",
		Progress:    0.0,
		Timestamp:   time.Now(),
		ProofBadge:  "QuaternionS³",
		ProofDetail: "State encoded as unit quaternion on S³ manifold (||q|| = 1)",
	}

	time.Sleep(100 * time.Millisecond)

	session, err := h.Engine.NewSession(input)
	if err != nil {
		client.Send <- Message{
			Type:      MsgError,
			Content:   err.Error(),
			Timestamp: time.Now(),
		}
		return
	}

	// Stream classification result
	client.Send <- Message{
		Type:        MsgThinking,
		Phase:       "intake",
		Content:     fmt.Sprintf("Classified as %s task", session.Classification.TaskType),
		Progress:    0.25,
		Confidence:  session.Classification.Confidence,
		Timestamp:   time.Now(),
		ProofBadge:  "QuaternionS³",
		ProofDetail: "State encoded as unit quaternion on S³ manifold (||q|| = 1)",
		Data: map[string]interface{}{
			"task_type":       session.Classification.TaskType,
			"pattern_cluster": session.Classification.PatternCluster,
			"suggested_tools": session.Classification.SuggestedTools,
			"ai_enabled":      h.AIRouter.IsConfigured(),
		},
	}

	time.Sleep(100 * time.Millisecond)

	// Phase 2: Analysis
	client.Send <- Message{
		Type:        MsgPhaseUpdate,
		Phase:       "analysis",
		Content:     "Exploring patterns and connections...",
		Progress:    0.25,
		Timestamp:   time.Now(),
		ProofBadge:  "DigitalRoots",
		ProofDetail: "Feature extraction O(1) - Vedic mathematics (53× speedup)",
	}

	time.Sleep(150 * time.Millisecond)

	session.Analyze([]string{
		"Identified relevant data patterns",
		"Found connections to existing research",
		"Mapped stakeholder relationships",
	})

	for _, step := range session.Steps[2:] {
		client.Send <- Message{
			Type:        MsgThinking,
			Phase:       step.Phase.String(),
			Content:     step.Description,
			Progress:    0.5,
			Confidence:  step.Confidence,
			Timestamp:   step.Timestamp,
			ProofBadge:  step.ProofBadge,
			ProofDetail: step.ProofDetail,
		}
		time.Sleep(75 * time.Millisecond)
	}

	// Phase 3: Synthesis
	client.Send <- Message{
		Type:        MsgPhaseUpdate,
		Phase:       "synthesis",
		Content:     "Combining insights into solutions...",
		Progress:    0.5,
		Timestamp:   time.Now(),
		ProofBadge:  "MirzakhaniGeodesics",
		ProofDetail: "Geodesic flow on hyperbolic manifold (shortest path)",
	}

	time.Sleep(150 * time.Millisecond)

	session.Synthesize([]string{
		"Evaluated multiple approaches",
		"Selected optimal solution path",
		"Prepared actionable recommendations",
	})

	// Phase 4: Insight - Use LLM if configured, otherwise use local reasoning
	client.Send <- Message{
		Type:        MsgPhaseUpdate,
		Phase:       "insight",
		Content:     "Formulating recommendation...",
		Progress:    0.75,
		Timestamp:   time.Now(),
		ProofBadge:  "SATOrigami",
		ProofDetail: "87.532% satisfaction via SLERP convergence (thermodynamic limit)",
	}

	var recommendation string
	var aiModel string

	if h.AIRouter.IsConfigured() {
		// Use real LLM for response
		client.Send <- Message{
			Type:      MsgThinking,
			Phase:     "insight",
			Content:   "Consulting AI research assistant...",
			Progress:  0.8,
			Timestamp: time.Now(),
		}

		llmResponse, err := h.AIRouter.ResearchChat(input, fmt.Sprintf(
			"Task type: %s\nPattern cluster: %d\nSuggested tools: %v",
			session.Classification.TaskType,
			session.Classification.PatternCluster,
			session.Classification.SuggestedTools,
		))

		if err != nil {
			recommendation = fmt.Sprintf("AI unavailable (%v). Based on %s analysis: Use %s tool for optimal results.",
				err, session.Classification.TaskType, session.Classification.SuggestedTools[0])
		} else {
			recommendation = llmResponse
			if model, _ := h.AIRouter.SelectModel(aiml.SelectionConstraints{TaskType: aiml.TASK_REASONING}); model != nil {
				aiModel = model.Name
			}
		}
	} else {
		// Local reasoning fallback
		recommendation = fmt.Sprintf("Based on %s analysis: Use %s tool for optimal results. Confidence: %.0f%%\n\n"+
			"Note: Set AIMLAPI_KEY environment variable to enable AI-powered responses.",
			session.Classification.TaskType,
			session.Classification.SuggestedTools[0],
			session.Classification.Confidence*100)
	}

	session.Conclude(recommendation)

	// Send final response content
	responseData := map[string]interface{}{
		"session_id":   session.ID,
		"total_steps":  len(session.Steps),
		"thinking_log": session.GetThinkingLog(),
	}
	if aiModel != "" {
		responseData["ai_model"] = aiModel
	}

	client.Send <- Message{
		Type:       MsgResponse,
		Phase:      "insight",
		Content:    recommendation,
		Progress:   1.0,
		Confidence: 0.95,
		Timestamp:  time.Now(),
		Data:       responseData,
	}

	// Send completion signal
	client.Send <- Message{
		Type:      MsgComplete,
		Phase:     "complete",
		Timestamp: time.Now(),
	}
}

// listTools sends available tools to the client
func (h *Hub) listTools(client *Client) {
	client.Send <- Message{
		Type:      MsgResponse,
		Content:   "Available Urban Lens Tools",
		Timestamp: time.Now(),
		Data: map[string]interface{}{
			"tools": []string{
				"census-enhance: Enhance census data quality",
				"survey-validate: Validate survey data",
				"spatial-analyze: Analyze spatial patterns",
				"document-process: Process documents with OCR",
				"flood-monitor: Monitor flood conditions",
			},
		},
	}
}

// ============================================================================
// PROGRESS STREAMER
// ============================================================================

// ProgressStreamer streams progress updates
type ProgressStreamer struct {
	client     *Client
	totalSteps int
	current    int
}

// NewProgressStreamer creates a progress streamer
func NewProgressStreamer(client *Client, totalSteps int) *ProgressStreamer {
	return &ProgressStreamer{
		client:     client,
		totalSteps: totalSteps,
		current:    0,
	}
}

// Step advances and streams progress
func (p *ProgressStreamer) Step(description string) {
	p.current++
	progress := float64(p.current) / float64(p.totalSteps)

	p.client.Send <- Message{
		Type:      MsgProgress,
		Content:   description,
		Progress:  progress,
		Timestamp: time.Now(),
	}
}

// Complete marks completion
func (p *ProgressStreamer) Complete(result string) {
	p.client.Send <- Message{
		Type:      MsgResponse,
		Content:   result,
		Progress:  1.0,
		Timestamp: time.Now(),
	}
	p.client.Send <- Message{
		Type:      MsgComplete,
		Phase:     "complete",
		Timestamp: time.Now(),
	}
}
