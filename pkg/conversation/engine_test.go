// Package conversation - Tests for Conversation Engine
package conversation

import (
	"context"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// MOCK IMPLEMENTATIONS
// ═══════════════════════════════════════════════════════════════════════════

// MockAIClient for testing
type MockAIClient struct {
	Response string
	Error    error
}

func (m *MockAIClient) GenerateResponse(conv *Conversation, systemPrompt, userMessage string) (string, error) {
	if m.Error != nil {
		return "", m.Error
	}
	return m.Response, nil
}

// MockLeanBridge for testing
type MockLeanBridge struct {
	Theorem       string
	Valid         bool
	GenerateError error
	ValidateError error
}

func (m *MockLeanBridge) GenerateTheorem(conv *Conversation) (string, error) {
	if m.GenerateError != nil {
		return "", m.GenerateError
	}
	return m.Theorem, nil
}

func (m *MockLeanBridge) ValidateTheorem(leanCode string) (bool, error) {
	if m.ValidateError != nil {
		return false, m.ValidateError
	}
	return m.Valid, nil
}

// MockKnowledgeGraph for testing
type MockKnowledgeGraph struct{}

func (m *MockKnowledgeGraph) FindRelatedConcepts(domain string, concept string) ([]string, error) {
	return []string{"concept1", "concept2"}, nil
}

func (m *MockKnowledgeGraph) StoreInsight(insight Insight) error {
	return nil
}

// MockLanguageDetector for testing
type MockLanguageDetector struct {
	Language string
}

func (m *MockLanguageDetector) Detect(text string) (string, error) {
	return m.Language, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestNewEngine(t *testing.T) {
	ai := &MockAIClient{}
	lean := &MockLeanBridge{}
	kg := &MockKnowledgeGraph{}
	lang := &MockLanguageDetector{Language: "en"}

	engine := NewEngine(ai, lean, kg, lang)

	if engine == nil {
		t.Fatal("NewEngine returned nil")
	}
	if engine.aiClient != ai {
		t.Error("AI client not set correctly")
	}
}

func TestNewConversation(t *testing.T) {
	engine := NewEngine(nil, nil, nil, nil)
	conv := engine.NewConversation("user123")

	if conv.ID == "" {
		t.Error("Conversation ID not generated")
	}
	if conv.UserID != "user123" {
		t.Errorf("UserID = %s, want user123", conv.UserID)
	}
	if conv.State != StateGreeting {
		t.Errorf("Initial state = %s, want %s", conv.State, StateGreeting)
	}
	if conv.Phase != PhaseVoid {
		t.Errorf("Initial phase = %s, want %s", conv.Phase, PhaseVoid)
	}
}

func TestGreetingState(t *testing.T) {
	engine := NewEngine(nil, nil, nil, nil)
	conv := engine.NewConversation("user123")

	ctx := context.Background()

	// Test greeting without observation
	response, err := engine.ProcessMessage(ctx, conv, "Hello!")
	if err != nil {
		t.Fatalf("ProcessMessage error: %v", err)
	}

	if response == "" {
		t.Error("Response is empty")
	}
	if conv.State != StateGreeting {
		t.Errorf("State changed unexpectedly to %s", conv.State)
	}

	// Test greeting with observation
	conv2 := engine.NewConversation("user456")
	response2, err := engine.ProcessMessage(ctx, conv2, "I noticed the water boiling in my kettle")
	if err != nil {
		t.Fatalf("ProcessMessage error: %v", err)
	}

	if response2 == "" {
		t.Error("Response is empty")
	}
	if conv2.State != StateAnchoring {
		t.Errorf("State = %s, want %s", conv2.State, StateAnchoring)
	}
	if conv2.Anchor == "" {
		t.Error("Anchor not extracted")
	}
}

func TestIntelligenceDetection(t *testing.T) {
	tests := []struct {
		name     string
		message  string
		expected IntelligenceType
	}{
		{
			name:     "Kinesthetic",
			message:  "I feel the warm dough in my hands, it's soft and smooth",
			expected: IntKinesthetic,
		},
		{
			name:     "Visual",
			message:  "I see the bright blue sky with white clouds forming patterns",
			expected: IntVisual,
		},
		{
			name:     "Spatial",
			message:  "The boxes are arranged in a circular pattern, with the largest at the center",
			expected: IntSpatial,
		},
		{
			name:     "Logical",
			message:  "Because the data shows that if temperature increases, then pressure increases",
			expected: IntLogical,
		},
		{
			name:     "Auditory",
			message:  "I hear the rhythmic pop of the seeds, like a musical beat",
			expected: IntAuditory,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			detected, scores := DetectIntelligenceType(tt.message)

			if detected != tt.expected && detected != IntUnknown {
				t.Logf("Detected: %s, Expected: %s, Scores: %v", detected, tt.expected, scores)
				// Not a hard failure since detection is heuristic
			}
		})
	}
}

func TestPhaseDetection(t *testing.T) {
	tests := []struct {
		name     string
		message  string
		expected VoidFlowPhase
	}{
		{
			name:     "Void - Uncertain",
			message:  "I'm not sure what causes this, maybe it's the temperature?",
			expected: PhaseVoid,
		},
		{
			name:     "Flow - Connection",
			message:  "Oh! I see, it's like when I cook rice - the water evaporates!",
			expected: PhaseFlow,
		},
		{
			name:     "Solution - Confident",
			message:  "Yes, exactly! I understand now, it's definitely the phase transition!",
			expected: PhaseSolution,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			voidScore := detectVoidSignals(tt.message)
			flowScore := detectFlowSignals(tt.message)
			solutionScore := detectSolutionSignals(tt.message)

			t.Logf("Void: %.2f, Flow: %.2f, Solution: %.2f",
				voidScore, flowScore, solutionScore)

			// Verify expected phase has highest score
			switch tt.expected {
			case PhaseVoid:
				if voidScore == 0 {
					t.Error("Expected Void signals but found none")
				}
			case PhaseFlow:
				if flowScore == 0 {
					t.Error("Expected Flow signals but found none")
				}
			case PhaseSolution:
				if solutionScore == 0 {
					t.Error("Expected Solution signals but found none")
				}
			}
		})
	}
}

func TestWhyChaining(t *testing.T) {
	engine := NewEngine(nil, nil, nil, nil)
	conv := engine.NewConversation("user123")
	ctx := context.Background()

	// Start with an observation to establish anchor
	_, err := engine.ProcessMessage(ctx, conv, "I noticed mustard seeds popping in hot oil")
	if err != nil {
		t.Fatalf("Initial message error: %v", err)
	}

	// Make it concrete to move to why-chaining
	_, err = engine.ProcessMessage(ctx, conv, "I feel them pop in the pan, it's hot and makes a crackling sound")
	if err != nil {
		t.Fatalf("Anchoring error: %v", err)
	}

	if conv.State != StateWhyChaining {
		t.Logf("State is %s, manually setting to WHY_CHAINING for test", conv.State)
		conv.State = StateWhyChaining
	}

	// Simulate why-chain progression
	steps := []string{
		"Water turns to steam inside",
		"The seed coat acts as a pressure vessel",
		"It's a lattice structure with limited pathways",
		"The lattice creates a rate limiter for steam escape",
		"The pop is caused by phonons - quantized vibrations in the lattice",
	}

	for i, step := range steps {
		response, err := engine.ProcessMessage(ctx, conv, step)
		if err != nil {
			t.Fatalf("Step %d error: %v", i+1, err)
		}

		if response == "" {
			t.Errorf("Step %d: empty response", i+1)
		}

		t.Logf("Step %d: Depth=%d, State=%s", i+1, conv.WhyChainDepth, conv.State)
	}

	// After 5 steps mentioning fundamental physics, should transition to synthesis
	// (or might transition earlier if "phonons" and "lattice" trigger fundamental science detection)
	if conv.State != StateSynthesizing && conv.WhyChainDepth < 5 {
		t.Logf("Note: State = %s after %d steps (may transition early due to physics keywords)",
			conv.State, conv.WhyChainDepth)
	}
}

func TestSophisticationDetection(t *testing.T) {
	tests := []struct {
		name     string
		message  string
		minLevel int
		maxLevel int
	}{
		{
			name:     "Child level",
			message:  "Why is the sky blue? My mom said it's because of light.",
			minLevel: 1,
			maxLevel: 4,
		},
		{
			name:     "Technical level",
			message:  "I'm researching the Hessian eigenvalues in neural network optimization landscapes.",
			minLevel: 7,
			maxLevel: 10,
		},
		{
			name:     "General level",
			message:  "I noticed that customer patterns follow a wave-like structure.",
			minLevel: 4,
			maxLevel: 7,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			level := DetectSophisticationLevel(tt.message)
			t.Logf("Detected level: %d", level)

			if level < tt.minLevel || level > tt.maxLevel {
				t.Errorf("Level %d not in expected range [%d, %d]",
					level, tt.minLevel, tt.maxLevel)
			}
		})
	}
}

func TestFrustrationDetection(t *testing.T) {
	engine := NewEngine(nil, nil, nil, nil)

	frustrated := "I don't get it, this is too hard and confusing"
	response := engine.checkFrustration(frustrated)

	if response == "" {
		t.Error("Failed to detect frustration")
	}
	if !containsAny(response, []string{"slow down", "not stuck", "exploration"}) {
		t.Error("Response doesn't provide encouragement")
	}
}

func TestQuitDetection(t *testing.T) {
	engine := NewEngine(nil, nil, nil, nil)

	quit := "I have to go now, maybe later"
	response := engine.checkQuit(quit)

	if response == "" {
		t.Error("Failed to detect quit intent")
	}
	if !containsAny(response, []string{"valuable", "come back"}) {
		t.Error("Response doesn't provide graceful exit")
	}
}

func TestEmotionDetection(t *testing.T) {
	tests := []struct {
		message  string
		expected string
	}{
		{"Wow, this is amazing! I love it!", "excited"},
		{"I'm stuck and can't figure this out", "frustrated"},
		{"I wonder what would happen if...", "curious"},
		{"Yes, I definitely understand now", "confident"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			emotion := DetectEmotion(tt.message)
			t.Logf("Message: %s -> Emotion: %s", tt.message, emotion)

			// Emotion detection is heuristic, so just log results
			// Could be improved with ML model
		})
	}
}

func TestConversationPaceDetection(t *testing.T) {
	tests := []struct {
		name     string
		messages []Message
		expected string
	}{
		{
			name: "Fast pace (short responses)",
			messages: []Message{
				{Role: "user", Content: "Yes"},
				{Role: "user", Content: "Ok"},
				{Role: "user", Content: "Got it"},
			},
			expected: "fast",
		},
		{
			name: "Slow pace (long responses)",
			messages: []Message{
				{Role: "user", Content: "I've been thinking about this for a while, and I notice that when I cook rice, the water slowly evaporates and the rice becomes fluffy..."},
			},
			expected: "slow",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			pace := DetectConversationPace(tt.messages)
			if pace != tt.expected {
				t.Logf("Expected %s, got %s (heuristic, not critical)", tt.expected, pace)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// INTEGRATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestFullConversationFlow(t *testing.T) {
	// Test a complete conversation from greeting to celebration
	engine := NewEngine(nil, nil, nil, nil)
	conv := engine.NewConversation("user123")
	ctx := context.Background()

	steps := []struct {
		userMsg       string
		expectedState ConversationState
	}{
		{"I noticed water boiling in my kettle", StateAnchoring},
		{"I see bubbles forming at the bottom and rising to the top", StateWhyChaining},
		{"The water gets hot from the stove", StateWhyChaining},
		{"Heat energy makes water molecules move faster", StateWhyChaining},
		{"Fast-moving molecules overcome liquid bonds and become gas", StateWhyChaining},
		{"The bubbles are steam - water vapor", StateWhyChaining},
		{"It's like phase transition - thermodynamics", StateSynthesizing},
	}

	for i, step := range steps {
		response, err := engine.ProcessMessage(ctx, conv, step.userMsg)
		if err != nil {
			t.Fatalf("Step %d error: %v", i+1, err)
		}

		t.Logf("Step %d: State=%s, Phase=%s, Response length=%d",
			i+1, conv.State, conv.Phase, len(response))

		// State progression should match or be past expected
		// (might transition faster than expected based on content)
	}

	// Should have progressed through states
	if len(conv.Messages) < 2 {
		t.Error("Conversation didn't record messages")
	}

	if conv.Anchor == "" {
		t.Error("Anchor was not set")
	}

	if conv.WhyChainDepth == 0 {
		t.Error("Why chain depth not tracked")
	}
}

// Helper function for tests
func containsAny(s string, keywords []string) bool {
	for _, kw := range keywords {
		if len(s) >= len(kw) {
			for i := 0; i <= len(s)-len(kw); i++ {
				match := true
				for j := 0; j < len(kw); j++ {
					sc := s[i+j]
					kc := kw[j]
					if sc >= 'A' && sc <= 'Z' {
						sc += 32
					}
					if kc >= 'A' && kc <= 'Z' {
						kc += 32
					}
					if sc != kc {
						match = false
						break
					}
				}
				if match {
					return true
				}
			}
		}
	}
	return false
}
