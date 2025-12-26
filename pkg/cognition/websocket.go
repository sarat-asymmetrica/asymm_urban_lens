package cognition

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"sync"

	gorilla_ws "github.com/gorilla/websocket"
)

// ============================================================================
// WEBSOCKET SERVER - Real-time cognition streaming
// ============================================================================
//
// Streams cognitive events to WebSocket clients at Tesla 4.909 Hz
// Supports multiple concurrent sessions
// Handles interventions from clients
//
// ============================================================================

var upgrader = gorilla_ws.Upgrader{
	CheckOrigin: func(r *http.Request) bool {
		// Allow all origins for development
		// PRODUCTION: Implement proper origin checking
		return true
	},
	ReadBufferSize:  1024,
	WriteBufferSize: 4096, // Larger for event streaming
}

// CognitionWebSocket manages WebSocket connections for cognition streaming
type CognitionWebSocket struct {
	observer  *CognitionObserver
	clients   map[string]*wsClient // sessionID -> client
	clientsMu sync.RWMutex
}

// wsClient represents a WebSocket client
type wsClient struct {
	conn      *gorilla_ws.Conn
	sessionID string
	send      chan []byte
}

// NewCognitionWebSocket creates a new WebSocket server
func NewCognitionWebSocket(observer *CognitionObserver) *CognitionWebSocket {
	return &CognitionWebSocket{
		observer: observer,
		clients:  make(map[string]*wsClient),
	}
}

// HandleConnection upgrades HTTP to WebSocket and starts streaming
func (cws *CognitionWebSocket) HandleConnection(w http.ResponseWriter, r *http.Request) {
	// Extract session ID from query params
	sessionID := r.URL.Query().Get("session_id")
	if sessionID == "" {
		http.Error(w, "session_id required", http.StatusBadRequest)
		return
	}

	// Upgrade to WebSocket
	conn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		log.Printf("❌ WebSocket upgrade failed: %v", err)
		http.Error(w, "upgrade failed", http.StatusInternalServerError)
		return
	}

	// Create client
	client := &wsClient{
		conn:      conn,
		sessionID: sessionID,
		send:      make(chan []byte, 256),
	}

	// Register client
	cws.clientsMu.Lock()
	cws.clients[sessionID] = client
	cws.clientsMu.Unlock()

	log.Printf("✅ WebSocket client connected: session=%s", sessionID)

	// Send welcome message
	welcome := WSMessage{
		Type:      "connected",
		SessionID: sessionID,
		Data: map[string]interface{}{
			"message":          "🌊 Connected to cognition stream",
			"tesla_interval_ms": TeslaHarmonicMs,
			"tesla_frequency_hz": TeslaBaseFrequencyHz,
		},
	}

	if msg, err := json.Marshal(welcome); err == nil {
		client.send <- msg
	}

	// Start goroutines
	go cws.writePump(client)
	go cws.readPump(client, r.Context())

	// Get stream and start forwarding events
	stream, err := cws.observer.GetStream(sessionID)
	if err != nil {
		log.Printf("⚠️ Stream not found for session %s: %v", sessionID, err)
		return
	}

	go cws.streamToClient(client, stream)
}

// writePump sends messages to WebSocket client
func (cws *CognitionWebSocket) writePump(client *wsClient) {
	defer func() {
		client.conn.Close()
		cws.unregisterClient(client.sessionID)
	}()

	for message := range client.send {
		if err := client.conn.WriteMessage(gorilla_ws.TextMessage, message); err != nil {
			log.Printf("❌ WebSocket write error (session %s): %v", client.sessionID, err)
			return
		}
	}
}

// readPump receives messages from WebSocket client
func (cws *CognitionWebSocket) readPump(client *wsClient, ctx context.Context) {
	defer func() {
		client.conn.Close()
		cws.unregisterClient(client.sessionID)
	}()

	for {
		var msg WSMessage
		err := client.conn.ReadJSON(&msg)
		if err != nil {
			if gorilla_ws.IsUnexpectedCloseError(err, gorilla_ws.CloseGoingAway, gorilla_ws.CloseAbnormalClosure) {
				log.Printf("❌ WebSocket error (session %s): %v", client.sessionID, err)
			} else {
				log.Printf("🔌 WebSocket client disconnected: session=%s", client.sessionID)
			}
			return
		}

		log.Printf("📨 Received message from session %s: type=%s", client.sessionID, msg.Type)

		// Handle message
		if err := cws.handleMessage(ctx, client, msg); err != nil {
			log.Printf("❌ Message handling error (session %s): %v", client.sessionID, err)

			// Send error response
			errMsg := WSMessage{
				Type:      "error",
				SessionID: client.sessionID,
				Data: map[string]interface{}{
					"error": err.Error(),
				},
			}

			if msgBytes, err := json.Marshal(errMsg); err == nil {
				client.send <- msgBytes
			}
		}
	}
}

// streamToClient forwards events from stream to WebSocket
func (cws *CognitionWebSocket) streamToClient(client *wsClient, stream *ThoughtStream) {
	for event := range stream.EventChannel {
		// Wrap event in WSMessage
		msg := WSMessage{
			Type:      "event",
			SessionID: client.sessionID,
			Data:      event,
			Timestamp: event.Timestamp,
		}

		// Serialize to JSON
		msgBytes, err := json.Marshal(msg)
		if err != nil {
			log.Printf("❌ Failed to serialize event (session %s): %v", client.sessionID, err)
			continue
		}

		// Send to client (non-blocking)
		select {
		case client.send <- msgBytes:
			// Sent successfully
		default:
			log.Printf("⚠️ Client send buffer full (session %s), dropping event", client.sessionID)
		}
	}

	log.Printf("📊 Stream ended for session %s", client.sessionID)
}

// handleMessage processes incoming WebSocket messages
func (cws *CognitionWebSocket) handleMessage(ctx context.Context, client *wsClient, msg WSMessage) error {
	switch msg.Type {
	case "subscribe":
		// Already subscribed when connected, just acknowledge
		ack := WSMessage{
			Type:      "subscribed",
			SessionID: client.sessionID,
			Data: map[string]interface{}{
				"message": "✅ Subscribed to cognition stream",
			},
		}

		if msgBytes, err := json.Marshal(ack); err == nil {
			client.send <- msgBytes
		}

		return nil

	case "intervene":
		// Handle intervention request
		var req InterventionRequest
		dataBytes, err := json.Marshal(msg.Data)
		if err != nil {
			return fmt.Errorf("invalid intervention data: %w", err)
		}

		if err := json.Unmarshal(dataBytes, &req); err != nil {
			return fmt.Errorf("failed to parse intervention: %w", err)
		}

		// Process intervention (placeholder for now)
		if err := cws.handleIntervention(ctx, &req); err != nil {
			return fmt.Errorf("intervention failed: %w", err)
		}

		// Send acknowledgment
		ack := WSMessage{
			Type:      "intervention_ack",
			SessionID: client.sessionID,
			Data: map[string]interface{}{
				"message":        "✅ Intervention applied",
				"target_concept": req.TargetConcept,
				"action":         req.Action,
			},
		}

		if msgBytes, err := json.Marshal(ack); err == nil {
			client.send <- msgBytes
		}

		return nil

	case "ping":
		// Heartbeat
		pong := WSMessage{
			Type:      "pong",
			SessionID: client.sessionID,
		}

		if msgBytes, err := json.Marshal(pong); err == nil {
			client.send <- msgBytes
		}

		return nil

	default:
		return fmt.Errorf("unknown message type: %s", msg.Type)
	}
}

// handleIntervention processes an intervention request
func (cws *CognitionWebSocket) handleIntervention(ctx context.Context, req *InterventionRequest) error {
	// Get the stream
	stream, err := cws.observer.GetStream(req.SessionID)
	if err != nil {
		return err
	}

	if !stream.Active {
		return fmt.Errorf("session %s not active", req.SessionID)
	}

	// Emit an event about the intervention
	event := &CognitionEvent{
		SessionID: req.SessionID,
		Timestamp: stream.StartTime,
		EventType: EventPatternDetected,
		Regime:    stream.CurrentRegime,
		Message:   fmt.Sprintf("🎯 Intervention: %s on concept %s", req.Action, req.TargetConcept.String()[:8]),
		Metadata: map[string]interface{}{
			"intervention_action":   req.Action,
			"intervention_strength": req.Strength,
			"intervention_reason":   req.Reason,
		},
	}

	stream.EventChannel <- event
	stream.EventCount++

	log.Printf("🎯 Intervention applied: session=%s, action=%s, concept=%s",
		req.SessionID, req.Action, req.TargetConcept.String()[:8])

	return nil
}

// unregisterClient removes a client
func (cws *CognitionWebSocket) unregisterClient(sessionID string) {
	cws.clientsMu.Lock()
	defer cws.clientsMu.Unlock()

	if client, exists := cws.clients[sessionID]; exists {
		close(client.send)
		delete(cws.clients, sessionID)
		log.Printf("🔌 Client unregistered: session=%s", sessionID)
	}
}

// Broadcast sends a message to all connected clients
func (cws *CognitionWebSocket) Broadcast(msg WSMessage) {
	cws.clientsMu.RLock()
	defer cws.clientsMu.RUnlock()

	msgBytes, err := json.Marshal(msg)
	if err != nil {
		log.Printf("❌ Failed to serialize broadcast message: %v", err)
		return
	}

	for sessionID, client := range cws.clients {
		select {
		case client.send <- msgBytes:
			// Sent successfully
		default:
			log.Printf("⚠️ Broadcast: client %s buffer full, dropping message", sessionID)
		}
	}
}

// GetConnectedClients returns list of connected session IDs
func (cws *CognitionWebSocket) GetConnectedClients() []string {
	cws.clientsMu.RLock()
	defer cws.clientsMu.RUnlock()

	clients := make([]string, 0, len(cws.clients))
	for sessionID := range cws.clients {
		clients = append(clients, sessionID)
	}

	return clients
}
