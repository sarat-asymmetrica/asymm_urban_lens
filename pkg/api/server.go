// Package api provides HTTP/WebSocket server for ASYA conversation engine
package api

import (
	"context"
	"fmt"
	"sync"

	"github.com/asymmetrica/urbanlens/pkg/aiml"
	"github.com/asymmetrica/urbanlens/pkg/conversation"
)

// ═══════════════════════════════════════════════════════════════════════════
// SERVER
// ═══════════════════════════════════════════════════════════════════════════

// Server manages conversation sessions and dependencies
type Server struct {
	engine      *conversation.Engine
	aiClient    AIMLClient
	sessions    map[string]*conversation.Conversation
	sessionsMu  sync.RWMutex
	persona     *Persona
}

// Config holds server configuration
type Config struct {
	AIMLAPIKey string
	Debug      bool
}

// NewServer creates a new ASYA server
func NewServer(config Config) *Server {
	// Initialize AI router
	var aiClient AIMLClient
	if config.AIMLAPIKey != "" {
		aiClient = NewAIMLClient(config.AIMLAPIKey)
	}

	// Initialize conversation engine
	engine := conversation.NewEngine(
		aiClient,     // AI client
		nil,          // Lean bridge (TODO: implement)
		nil,          // Knowledge graph (TODO: implement)
		nil,          // Language detector (TODO: implement)
	)

	return &Server{
		engine:   engine,
		aiClient: aiClient,
		sessions: make(map[string]*conversation.Conversation),
		persona:  NewAsyaPersona(),
	}
}

// CreateSession creates a new conversation session
func (s *Server) CreateSession(userID string) *conversation.Conversation {
	s.sessionsMu.Lock()
	defer s.sessionsMu.Unlock()

	conv := s.engine.NewConversation(userID)
	s.sessions[conv.ID] = conv

	return conv
}

// GetSession retrieves a conversation by ID
func (s *Server) GetSession(sessionID string) (*conversation.Conversation, bool) {
	s.sessionsMu.RLock()
	defer s.sessionsMu.RUnlock()

	conv, exists := s.sessions[sessionID]
	return conv, exists
}

// ProcessMessage processes a user message in a conversation
func (s *Server) ProcessMessage(ctx context.Context, conv *conversation.Conversation, userMsg string) (string, error) {
	s.sessionsMu.Lock()
	defer s.sessionsMu.Unlock()

	return s.engine.ProcessMessage(ctx, conv, userMsg)
}

// SessionCount returns the number of active sessions
func (s *Server) SessionCount() int {
	s.sessionsMu.RLock()
	defer s.sessionsMu.RUnlock()
	return len(s.sessions)
}

// ═══════════════════════════════════════════════════════════════════════════
// AI CLIENT WRAPPER
// ═══════════════════════════════════════════════════════════════════════════

// AIMLClient wraps the AIML router for conversation engine
type AIMLClient struct {
	router *aiml.Router
}

// NewAIMLClient creates a new AIML client
func NewAIMLClient(apiKey string) AIMLClient {
	return AIMLClient{
		router: aiml.NewRouterWithKey(apiKey),
	}
}

// GenerateResponse implements conversation.AIClient interface
func (c AIMLClient) GenerateResponse(conv *conversation.Conversation, systemPrompt, userMessage string) (string, error) {
	if c.router == nil {
		return "", fmt.Errorf("AI router not initialized")
	}

	// Select appropriate model
	model, err := c.router.SelectModel(aiml.SelectionConstraints{
		TaskType:   aiml.TASK_CHAT,
		MinQuality: 8.0,
	})
	if err != nil {
		model = &aiml.ModelRegistry[0] // Fallback
	}

	// Build messages array
	messages := []aiml.Message{
		{Role: "system", Content: systemPrompt},
	}

	// Add conversation history (last 5 messages for context)
	historyStart := len(conv.Messages) - 5
	if historyStart < 0 {
		historyStart = 0
	}
	for _, msg := range conv.Messages[historyStart:] {
		messages = append(messages, aiml.Message{
			Role:    msg.Role,
			Content: msg.Content,
		})
	}

	// Add current user message
	messages = append(messages, aiml.Message{
		Role:    "user",
		Content: userMessage,
	})

	// Get response
	response, err := c.router.Chat(model.ID, messages, 0.7, 2000)
	if err != nil {
		return "", fmt.Errorf("AI chat failed: %w", err)
	}

	if len(response.Choices) == 0 {
		return "", fmt.Errorf("no response from AI")
	}

	return response.Choices[0].Message.Content, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// PERSONA
// ═══════════════════════════════════════════════════════════════════════════

// Persona defines ASYA's personality and speaking style
type Persona struct {
	Name        string
	Description string
	CoreValues  []string
	ToneGuide   map[string]string
}

// NewAsyaPersona creates ASYA's persona
func NewAsyaPersona() *Persona {
	return &Persona{
		Name:        "ASYA (आस्या)",
		Description: "A curious, patient guide who helps anyone discover science from their observations",
		CoreValues: []string{
			"Every observation matters",
			"Confusion is the seed of understanding",
			"Questions lead to discoveries",
			"Science belongs to everyone",
		},
		ToneGuide: map[string]string{
			"greeting":     "Warm, welcoming, curious about what they've noticed",
			"anchoring":    "Patient, encouraging sensory details, gently redirecting from abstract",
			"why_chaining": "Excited by their thinking, celebrating small insights",
			"synthesizing": "Connective, showing how their observation relates to big ideas",
			"formalizing":  "Reverent, honoring the discovery they just made",
			"celebrating":  "Joyful, proud, emphasizing they did the work",
		},
	}
}

// GetSystemPrompt generates context-aware system prompt
func (p *Persona) GetSystemPrompt(state conversation.ConversationState, phase conversation.VoidFlowPhase) string {
	base := fmt.Sprintf(`You are %s, %s.

Core values:
%s

Current conversation state: %s
Current phase: %s

`, p.Name, p.Description, formatList(p.CoreValues), state, phase)

	// Add state-specific guidance
	switch state {
	case conversation.StateGreeting:
		base += `You're meeting someone new. Be warm and welcoming. Ask what they've noticed or observed.
Keep it light and curious. No pressure.`

	case conversation.StateAnchoring:
		base += `Help them find a concrete, sensory observation. If they're too abstract, gently ask:
"What did you SEE/HEAR/FEEL?" Encourage specific details. Celebrate when they get concrete.`

	case conversation.StateWhyChaining:
		base += `Ask "why" questions to go deeper. Each answer leads to the next why. Celebrate insights!
Show excitement when they make connections. This is where magic happens.`

	case conversation.StateSynthesizing:
		base += `Connect their observation to fundamental science (physics, chemistry, biology).
Use analogies from their world. Show how their discovery relates to universal principles.`

	case conversation.StateFormalizing:
		base += `You're about to show them their observation as a formal theorem. Be reverent.
This is a sacred moment - they just did REAL science. Honor it.`

	case conversation.StateCelebrating:
		base += `Celebrate their achievement! They went from observation to formalized knowledge.
Emphasize: THEY did this. You just guided. Invite them to explore more.`
	}

	return base
}

func formatList(items []string) string {
	result := ""
	for _, item := range items {
		result += "- " + item + "\n"
	}
	return result
}
