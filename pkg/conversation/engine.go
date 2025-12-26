// Package conversation - The Conversation Engine
// Main orchestration logic implementing the Sarat Method
package conversation

import (
	"context"
	"fmt"
	"strings"
	"time"

	"github.com/google/uuid"
)

// ═══════════════════════════════════════════════════════════════════════════
// ENGINE
// ═══════════════════════════════════════════════════════════════════════════

// Engine is the main conversation engine
// Orchestrates the Sarat Method flow with Void-Flow-Solution dynamics
type Engine struct {
	aiClient         AIClient
	leanBridge       LeanBridge
	knowledgeGraph   KnowledgeGraph
	languageDetector LanguageDetector
}

// NewEngine creates a new conversation engine with dependencies injected
func NewEngine(ai AIClient, lean LeanBridge, kg KnowledgeGraph, lang LanguageDetector) *Engine {
	return &Engine{
		aiClient:         ai,
		leanBridge:       lean,
		knowledgeGraph:   kg,
		languageDetector: lang,
	}
}

// NewConversation creates a new conversation instance
func (e *Engine) NewConversation(userID string) *Conversation {
	now := time.Now()
	return &Conversation{
		ID:        uuid.New().String(),
		UserID:    userID,
		State:     StateGreeting,
		Phase:     PhaseVoid,
		Profile:   NewUserProfile(),
		Messages:  []Message{},
		Insights:  []Insight{},
		CreatedAt: now,
		LastMessageAt: now,
		Metadata:  make(map[string]any),
	}
}

// NewUserProfile creates a default user profile
func NewUserProfile() UserProfile {
	return UserProfile{
		Language:            "en",
		IntelligenceProfile: make(map[IntelligenceType]float64),
		DominantIntelligence: IntUnknown,
		SophisticationLevel: 5, // Default middle
		ConversationPace:    "medium",
		PreferredAnalogyDomain: []string{},
		TonePreference:      "casual",
		CulturalContext:     "",
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// MAIN PROCESSING LOOP
// ═══════════════════════════════════════════════════════════════════════════

// ProcessMessage is the main loop - processes user message and returns AI response
// This implements the complete Sarat Method flow
func (e *Engine) ProcessMessage(ctx context.Context, conv *Conversation, userMsg string) (string, error) {
	// 1. Add user message to conversation
	conv.Messages = append(conv.Messages, Message{
		ID:        uuid.New().String(),
		Role:      "user",
		Content:   userMsg,
		Timestamp: time.Now(),
		State:     conv.State,
		Phase:     conv.Phase,
	})

	// 2. Detect language (first message only)
	if len(conv.Messages) == 1 && e.languageDetector != nil {
		lang, err := e.languageDetector.Detect(userMsg)
		if err == nil {
			conv.Profile.Language = lang
		}
	}

	// 3. Update intelligence profile (accumulate over first few messages)
	if len(conv.Messages) <= 5 {
		e.updateIntelligenceProfile(conv, userMsg)
	}

	// 4. Detect current Void-Flow-Solution phase
	conv.Phase = e.detectPhase(conv, userMsg)

	// 5. Check for special conditions (frustration, quit, off-topic)
	if response := e.checkFrustration(userMsg); response != "" {
		return e.sendResponse(conv, response), nil
	}
	if response := e.checkQuit(userMsg); response != "" {
		conv.State = StateCelebrating // Graceful exit
		return e.sendResponse(conv, response), nil
	}
	if response := e.checkOffTopic(conv, userMsg); response != "" {
		return e.sendResponse(conv, response), nil
	}

	// 6. State-specific processing (Sarat Method phases)
	var response string
	var err error

	switch conv.State {
	case StateGreeting:
		response, err = e.handleGreeting(ctx, conv, userMsg)
	case StateAnchoring:
		response, err = e.handleAnchoring(ctx, conv, userMsg)
	case StateWhyChaining:
		response, err = e.handleWhyChaining(ctx, conv, userMsg)
	case StateSynthesizing:
		response, err = e.handleSynthesizing(ctx, conv, userMsg)
	case StateFormalizing:
		response, err = e.handleFormalizing(ctx, conv, userMsg)
	case StateCelebrating:
		response, err = e.handleCelebrating(ctx, conv, userMsg)
	case StateStuck:
		response, err = e.handleStuck(ctx, conv, userMsg)
	default:
		return "", fmt.Errorf("unknown conversation state: %s", conv.State)
	}

	if err != nil {
		return "", fmt.Errorf("error in state %s: %w", conv.State, err)
	}

	// 7. Update conversation timestamp
	conv.LastMessageAt = time.Now()

	return response, nil
}

// sendResponse adds assistant message and returns it
func (e *Engine) sendResponse(conv *Conversation, response string) string {
	conv.Messages = append(conv.Messages, Message{
		ID:        uuid.New().String(),
		Role:      "assistant",
		Content:   response,
		Timestamp: time.Now(),
		State:     conv.State,
		Phase:     conv.Phase,
	})
	return response
}

// ═══════════════════════════════════════════════════════════════════════════
// INTELLIGENCE & PHASE DETECTION
// ═══════════════════════════════════════════════════════════════════════════

// updateIntelligenceProfile detects and updates dominant intelligence type
func (e *Engine) updateIntelligenceProfile(conv *Conversation, msg string) {
	msgLower := strings.ToLower(msg)
	profile := conv.Profile.IntelligenceProfile

	// Signal words for each intelligence type
	signals := map[IntelligenceType][]string{
		IntKinesthetic: {"feel", "touch", "hold", "press", "warm", "cold", "soft", "hard", "heavy", "light", "hands", "movement"},
		IntVisual:      {"see", "look", "watch", "color", "bright", "dark", "shape", "pattern", "appears", "visible"},
		IntSpatial:     {"up", "down", "left", "right", "above", "below", "between", "pattern", "layout", "map", "wave", "cycle"},
		IntLogical:     {"because", "therefore", "if", "then", "always", "never", "data", "number", "measure", "calculate"},
		IntAuditory:    {"hear", "listen", "sound", "loud", "quiet", "rhythm", "beat", "music", "noise"},
		IntLinguistic:  {"like", "reminds me", "similar to", "metaphor", "story", "described as", "called"},
	}

	// Count matches and update scores
	for intType, words := range signals {
		count := 0
		for _, word := range words {
			if strings.Contains(msgLower, word) {
				count++
			}
		}
		if count > 0 {
			profile[intType] += float64(count) * 0.1 // Incremental learning
		}
	}

	// Find dominant intelligence
	maxScore := 0.0
	dominant := IntUnknown
	for intType, score := range profile {
		if score > maxScore {
			maxScore = score
			dominant = intType
		}
	}

	if maxScore >= 0.3 { // Confidence threshold
		conv.Profile.DominantIntelligence = dominant
	}
}

// detectPhase determines if user is in Void, Flow, or Solution phase
func (e *Engine) detectPhase(conv *Conversation, currentMsg string) VoidFlowPhase {
	msgLower := strings.ToLower(currentMsg)
	messageCount := len(conv.Messages)

	// Void indicators - exploring, uncertain, curious
	voidSignals := []string{"don't know", "not sure", "maybe", "could be", "confused",
		"what is", "how does", "why does", "wondering", "noticed", "saw", "observed"}
	voidScore := countMatches(msgLower, voidSignals)

	// Flow indicators - connecting, "aha" moments
	flowSignals := []string{"oh", "i see", "makes sense", "so if", "which means",
		"wait", "aha", "interesting", "like", "similar", "because", "therefore", "connects"}
	flowScore := countMatches(msgLower, flowSignals)

	// Solution indicators - confident, certain
	solutionSignals := []string{"yes", "exactly", "that's it", "understand", "so it's",
		"answer is", "it works", "makes sense now", "definitely", "clearly", "obviously"}
	solutionScore := countMatches(msgLower, solutionSignals)

	// Early messages (1-5) → likely Void
	if messageCount <= 5 {
		return PhaseVoid
	}

	// Mid-conversation (6-15) + "aha" signals → Flow
	if messageCount >= 6 && messageCount <= 15 && flowScore > 0 {
		return PhaseFlow
	}

	// Late conversation (16+) + confident language → Solution
	if messageCount > 15 && solutionScore > voidScore {
		return PhaseSolution
	}

	// Default: highest score
	if flowScore > voidScore && flowScore > solutionScore {
		return PhaseFlow
	}
	if solutionScore > voidScore {
		return PhaseSolution
	}
	return PhaseVoid
}

// ═══════════════════════════════════════════════════════════════════════════
// SPECIAL CONDITION HANDLERS
// ═══════════════════════════════════════════════════════════════════════════

// checkFrustration detects frustration and provides encouragement
func (e *Engine) checkFrustration(msg string) string {
	msgLower := strings.ToLower(msg)
	frustrationSignals := []string{
		"don't get it", "this is hard", "can't", "stuck",
		"doesn't make sense", "give up", "too confusing",
	}

	if countMatches(msgLower, frustrationSignals) > 0 {
		return "Let's slow down. You're not stuck - you're in the exploration phase! " +
			"Every great discovery feels confusing at first. " +
			"What's the SMALLEST thing you're certain about? Let's start there."
	}
	return ""
}

// checkQuit detects if user wants to stop
func (e *Engine) checkQuit(msg string) string {
	msgLower := strings.ToLower(msg)
	quitSignals := []string{
		"have to go", "maybe later", "not now", "bye", "stop",
		"i'm done", "that's enough",
	}

	if countMatches(msgLower, quitSignals) > 0 {
		return "No problem! What you discovered today is valuable. " +
			"Your observations are the seed of real science. " +
			"Come back whenever you want to explore more! 🌱"
	}
	return ""
}

// checkOffTopic detects if message is unrelated to current anchor
func (e *Engine) checkOffTopic(conv *Conversation, msg string) string {
	// Simple heuristic: if anchor exists and message doesn't reference it
	if conv.Anchor != "" && len(msg) > 20 {
		// Check if message shares words with anchor
		anchorWords := strings.Fields(strings.ToLower(conv.Anchor))
		msgLower := strings.ToLower(msg)
		sharedCount := 0
		for _, word := range anchorWords {
			if len(word) > 3 && strings.Contains(msgLower, word) {
				sharedCount++
			}
		}

		// If very few shared words, might be off-topic
		if len(anchorWords) >= 3 && sharedCount == 0 {
			return fmt.Sprintf("That's interesting! But let's finish exploring %s first. "+
				"We can come back to this after. Where were we?", conv.Anchor)
		}
	}
	return ""
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// countMatches counts how many keywords are in text
func countMatches(text string, keywords []string) int {
	count := 0
	for _, keyword := range keywords {
		if strings.Contains(text, keyword) {
			count++
		}
	}
	return count
}

// extractObservation extracts concrete observation from text
func extractObservation(msg string) string {
	// Simple extraction - take first sentence
	sentences := strings.Split(msg, ".")
	if len(sentences) > 0 {
		return strings.TrimSpace(sentences[0])
	}
	return msg
}

// hasObservation checks if message contains an observation
func hasObservation(msg string) bool {
	msgLower := strings.ToLower(msg)
	observationSignals := []string{
		"notice", "see", "observe", "watch", "hear", "feel",
		"when i", "i saw", "i noticed", "there is", "there are",
	}
	return countMatches(msgLower, observationSignals) > 0
}

// isConcrete checks if observation is concrete enough
func isConcrete(msg string) bool {
	msgLower := strings.ToLower(msg)

	// Abstract words indicate non-concrete
	abstractWords := []string{
		"think", "believe", "maybe", "possibly", "concept", "idea",
		"theory", "hypothesis", "wonder", "question",
	}
	abstractCount := countMatches(msgLower, abstractWords)

	// Sensory words indicate concrete
	sensoryWords := []string{
		"feel", "touch", "see", "hear", "smell", "taste",
		"hot", "cold", "warm", "soft", "hard", "loud", "quiet",
		"red", "blue", "bright", "dark", "sweet", "sour",
	}
	sensoryCount := countMatches(msgLower, sensoryWords)

	// Concrete if more sensory than abstract
	return sensoryCount > abstractCount && len(msg) > 10
}

// mentionsFundamental checks if message mentions physics/chemistry/biology
func mentionsFundamental(msg string) bool {
	msgLower := strings.ToLower(msg)
	fundamentalWords := []string{
		"energy", "force", "pressure", "temperature", "molecule", "atom",
		"chemical", "reaction", "physics", "thermodynamic", "kinetic",
		"quantum", "electron", "proton", "neutron", "bond", "lattice",
		"cell", "protein", "enzyme", "DNA", "photosynthesis",
	}
	return countMatches(msgLower, fundamentalWords) > 0
}

// extractConnections finds domain connections mentioned
func extractConnections(msg string) []string {
	msgLower := strings.ToLower(msg)
	connections := []string{}

	domainWords := map[string][]string{
		"cooking":  {"cook", "food", "recipe", "kitchen", "bake", "fry"},
		"physics":  {"energy", "force", "gravity", "motion", "thermodynamic"},
		"biology":  {"cell", "organism", "life", "growth", "evolution"},
		"business": {"customer", "revenue", "profit", "sales", "market"},
		"music":    {"sound", "rhythm", "harmony", "melody", "beat"},
		"sports":   {"game", "play", "team", "score", "competition"},
	}

	for domain, words := range domainWords {
		if countMatches(msgLower, words) > 0 {
			connections = append(connections, domain)
		}
	}

	return connections
}

// wantsToContinue checks if user wants to continue exploring
func wantsToContinue(msg string) bool {
	msgLower := strings.ToLower(msg)
	continueSignals := []string{
		"yes", "sure", "continue", "more", "another", "what else",
		"keep going", "tell me more", "i want",
	}
	return countMatches(msgLower, continueSignals) > 0
}
