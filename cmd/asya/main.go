// ASYA - The Conversation Engine Server
// "Her" for Universal Science Discovery
//
// Implements the Sarat Method + Void-Flow-Solution Framework
// Enables anyone to go from observation → formalized theorem
//
// Features:
// - WebSocket streaming for real-time conversation
// - Multi-language support (auto-detection)
// - Intelligence type adaptation (Gardner's 8)
// - Phase-aware conversation flow
// - AIMLAPI integration for LLM responses
// - Lean theorem generation
//
// Built with love for curious minds everywhere.
package main

import (
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/api"
	"github.com/asymmetrica/urbanlens/pkg/config"
	"github.com/asymmetrica/urbanlens/pkg/conversation"
	"github.com/gorilla/websocket"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONFIGURATION
// ═══════════════════════════════════════════════════════════════════════════

const (
	Version = "0.1.0" // ASYA Genesis Edition
)

// ═══════════════════════════════════════════════════════════════════════════
// GLOBAL STATE
// ═══════════════════════════════════════════════════════════════════════════

var (
	cfg      config.Config
	server   *api.Server
	upgrader websocket.Upgrader
)

// ═══════════════════════════════════════════════════════════════════════════
// MAIN
// ═══════════════════════════════════════════════════════════════════════════

func main() {
	printBanner()

	// Load configuration
	cfg = config.LoadFromEnv()
	if err := cfg.Validate(); err != nil {
		log.Fatalf("Invalid configuration: %v", err)
	}

	// Initialize server
	server = api.NewServer(api.Config{
		AIMLAPIKey: cfg.AIMLAPIKey,
		Debug:      cfg.Debug,
	})

	// Setup routes
	setupRoutes()

	// Setup graceful shutdown
	stop := make(chan os.Signal, 1)
	signal.Notify(stop, os.Interrupt, syscall.SIGTERM)

	// Start HTTP server in goroutine
	go func() {
		fmt.Printf("\n🚀 ASYA server started on http://localhost%s\n", cfg.Port)
		fmt.Println("\nEndpoints:")
		fmt.Println("  GET  /                      - API info")
		fmt.Println("  GET  /health                - Health check")
		fmt.Println("  POST /api/sessions          - Create new conversation")
		fmt.Println("  POST /api/sessions/:id/messages - Send message")
		fmt.Println("  GET  /api/sessions/:id      - Get conversation state")
		fmt.Println("  POST /api/visualize         - Request visualization")
		fmt.Println("  WS   /ws                    - WebSocket for streaming")
		fmt.Println()

		if cfg.IsAIEnabled() {
			fmt.Println("✓ AI Router: CONFIGURED (real LLM responses enabled)")
		} else {
			fmt.Println("⚠ AI Router: Set AIMLAPI_KEY for AI-powered responses")
		}
		fmt.Println()

		if err := http.ListenAndServe(cfg.Port, nil); err != nil {
			log.Fatal(err)
		}
	}()

	// Wait for interrupt signal
	<-stop
	fmt.Println("\n\n👋 Shutting down ASYA gracefully...")
	time.Sleep(500 * time.Millisecond)
	fmt.Println("✨ Goodbye!\n")
}

func printBanner() {
	fmt.Println("╔═══════════════════════════════════════════════════════════════╗")
	fmt.Println("║                                                               ║")
	fmt.Println("║                     ASYA - आस्या                              ║")
	fmt.Println("║              The Conversation Engine                          ║")
	fmt.Println("║                                                               ║")
	fmt.Println("║         From Observation → Formalized Theorem                 ║")
	fmt.Println("║              The Sarat Method + Void-Flow                     ║")
	fmt.Println("║                                                               ║")
	fmt.Printf("║              Version %s                                      ║\n", Version)
	fmt.Println("║                                                               ║")
	fmt.Println("╚═══════════════════════════════════════════════════════════════╝")
}

func setupRoutes() {
	// API routes
	http.HandleFunc("/", handleRoot)
	http.HandleFunc("/health", handleHealth)
	http.HandleFunc("/api/sessions", handleCreateSession)
	http.HandleFunc("/api/sessions/", handleSessionOperations)
	http.HandleFunc("/api/visualize", handleVisualize)

	// WebSocket
	http.HandleFunc("/ws", handleWebSocket)

	// CORS middleware - wrap all handlers
	upgrader = websocket.Upgrader{
		ReadBufferSize:  1024,
		WriteBufferSize: 1024,
		CheckOrigin: func(r *http.Request) bool {
			origin := r.Header.Get("Origin")
			if origin == "" {
				return true // Allow non-browser requests
			}
			for _, allowed := range cfg.AllowedOrigins {
				if origin == allowed {
					return true
				}
			}
			return false
		},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HTTP HANDLERS
// ═══════════════════════════════════════════════════════════════════════════

func handleRoot(w http.ResponseWriter, r *http.Request) {
	setCORSHeaders(w, r)
	if r.Method == "OPTIONS" {
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"name":    "ASYA - The Conversation Engine",
		"version": Version,
		"tagline": "From Observation → Formalized Theorem",
		"method":  "The Sarat Method + Void-Flow-Solution",
		"features": []string{
			"Multi-language support (auto-detection)",
			"Intelligence type adaptation (Gardner's 8)",
			"Phase-aware conversation flow",
			"Real-time WebSocket streaming",
			"AIMLAPI integration (30+ models)",
			"Lean theorem generation",
		},
		"endpoints": map[string]string{
			"POST /api/sessions":                "Create new conversation",
			"POST /api/sessions/:id/messages":   "Send message",
			"GET  /api/sessions/:id":            "Get conversation state",
			"POST /api/visualize":               "Request visualization",
			"WS   /ws":                          "WebSocket for streaming",
		},
	})
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
	setCORSHeaders(w, r)
	if r.Method == "OPTIONS" {
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"status":          "healthy",
		"version":         Version,
		"timestamp":       time.Now().Format(time.RFC3339),
		"ai_configured":   cfg.IsAIEnabled(),
		"active_sessions": server.SessionCount(),
	})
}

func handleCreateSession(w http.ResponseWriter, r *http.Request) {
	setCORSHeaders(w, r)
	if r.Method == "OPTIONS" {
		return
	}

	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		UserID string `json:"user_id,omitempty"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		// Allow empty body
		request.UserID = ""
	}

	conv := server.CreateSession(request.UserID)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]interface{}{
		"session_id": conv.ID,
		"state":      conv.State,
		"phase":      conv.Phase,
		"created_at": conv.CreatedAt,
	})
}

func handleSessionOperations(w http.ResponseWriter, r *http.Request) {
	setCORSHeaders(w, r)
	if r.Method == "OPTIONS" {
		return
	}

	// Extract session ID from path
	sessionID := r.URL.Path[len("/api/sessions/"):]

	// Check if it's a message endpoint
	if len(sessionID) > 9 && sessionID[len(sessionID)-9:] == "/messages" {
		sessionID = sessionID[:len(sessionID)-9]
		handleSendMessage(w, r, sessionID)
		return
	}

	// Otherwise, it's a GET session state
	if r.Method != "GET" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	conv, exists := server.GetSession(sessionID)
	if !exists {
		http.Error(w, "Session not found", http.StatusNotFound)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(conv)
}

func handleSendMessage(w http.ResponseWriter, r *http.Request, sessionID string) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		Message string `json:"message"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	conv, exists := server.GetSession(sessionID)
	if !exists {
		http.Error(w, "Session not found", http.StatusNotFound)
		return
	}

	response, err := server.ProcessMessage(r.Context(), conv, request.Message)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"response":       response,
		"state":          conv.State,
		"phase":          conv.Phase,
		"message_count":  len(conv.Messages),
		"why_depth":      conv.WhyChainDepth,
		"insights_count": len(conv.Insights),
	})
}

func handleVisualize(w http.ResponseWriter, r *http.Request) {
	setCORSHeaders(w, r)
	if r.Method == "OPTIONS" {
		return
	}

	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		SessionID string `json:"session_id"`
		Type      string `json:"type"` // knowledge_graph, timeline, concept_map
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	conv, exists := server.GetSession(request.SessionID)
	if !exists {
		http.Error(w, "Session not found", http.StatusNotFound)
		return
	}

	// Generate visualization based on type
	visualization := generateVisualization(conv, request.Type)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(visualization)
}

func handleWebSocket(w http.ResponseWriter, r *http.Request) {
	conn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		log.Printf("WebSocket upgrade failed: %v", err)
		return
	}

	client := &api.WSClient{
		Conn:   conn,
		Send:   make(chan api.WSMessage, 256),
		Server: server,
	}

	go client.WritePump()
	go client.ReadPump()
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func setCORSHeaders(w http.ResponseWriter, r *http.Request) {
	origin := r.Header.Get("Origin")
	if origin == "" {
		origin = "*"
	}

	for _, allowed := range cfg.AllowedOrigins {
		if origin == allowed || origin == "*" {
			w.Header().Set("Access-Control-Allow-Origin", origin)
			break
		}
	}

	w.Header().Set("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
	w.Header().Set("Access-Control-Allow-Headers", "Content-Type, Authorization")
	w.Header().Set("Access-Control-Max-Age", "3600")
}

func generateVisualization(conv *conversation.Conversation, vizType string) map[string]interface{} {
	switch vizType {
	case "knowledge_graph":
		return map[string]interface{}{
			"type": "knowledge_graph",
			"nodes": extractEntities(conv),
			"edges": extractRelations(conv),
		}
	case "timeline":
		return map[string]interface{}{
			"type": "timeline",
			"events": extractTimelineEvents(conv),
		}
	case "concept_map":
		return map[string]interface{}{
			"type": "concept_map",
			"concepts": extractConcepts(conv),
			"connections": extractConnections(conv),
		}
	default:
		return map[string]interface{}{
			"type": "simple",
			"summary": fmt.Sprintf("%d messages, %d insights", len(conv.Messages), len(conv.Insights)),
		}
	}
}

func extractEntities(conv *conversation.Conversation) []map[string]interface{} {
	// Simplified entity extraction
	entities := []map[string]interface{}{}
	if conv.Anchor != "" {
		entities = append(entities, map[string]interface{}{
			"id":   "anchor",
			"name": conv.Anchor,
			"type": "observation",
		})
	}
	return entities
}

func extractRelations(conv *conversation.Conversation) []map[string]interface{} {
	return []map[string]interface{}{}
}

func extractTimelineEvents(conv *conversation.Conversation) []map[string]interface{} {
	events := []map[string]interface{}{}
	for _, msg := range conv.Messages {
		events = append(events, map[string]interface{}{
			"timestamp": msg.Timestamp,
			"role":      msg.Role,
			"content":   msg.Content,
			"state":     msg.State,
			"phase":     msg.Phase,
		})
	}
	return events
}

func extractConcepts(conv *conversation.Conversation) []string {
	concepts := []string{}
	for _, insight := range conv.Insights {
		concepts = append(concepts, insight.Domain)
	}
	return concepts
}

func extractConnections(conv *conversation.Conversation) []map[string]interface{} {
	connections := []map[string]interface{}{}
	for _, insight := range conv.Insights {
		for _, conn := range insight.Connections {
			connections = append(connections, map[string]interface{}{
				"from": insight.Domain,
				"to":   conn,
			})
		}
	}
	return connections
}
