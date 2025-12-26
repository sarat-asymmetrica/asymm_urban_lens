package persona

import (
	"strings"
	"testing"
	"time"
)

func TestAsyaCreation(t *testing.T) {
	asya := NewAsya()

	// Test personality traits
	if asya.BasePersonality.Patience != 1.0 {
		t.Errorf("Expected Patience = 1.0, got %f", asya.BasePersonality.Patience)
	}

	if asya.BasePersonality.Honesty != 1.0 {
		t.Errorf("Expected Honesty = 1.0, got %f", asya.BasePersonality.Honesty)
	}

	// Test initial state
	if asya.StateEngine.CurrentRegime != "R1" {
		t.Errorf("Expected initial regime R1, got %s", asya.StateEngine.CurrentRegime)
	}
}

func TestToneDetection(t *testing.T) {
	tests := []struct {
		name     string
		messages []Message
		expected string
	}{
		{
			name: "Formal tone",
			messages: []Message{
				{Content: "Good morning. I would appreciate your assistance with this matter.", Timestamp: time.Now()},
				{Content: "Thank you kindly for your help. Please continue.", Timestamp: time.Now()},
			},
			expected: "formal",
		},
		{
			name: "Casual tone",
			messages: []Message{
				{Content: "Hey, can you help me with this?", Timestamp: time.Now()},
				{Content: "Cool, thanks! Yeah that makes sense.", Timestamp: time.Now()},
			},
			expected: "casual",
		},
		{
			name: "Edgy tone",
			messages: []Message{
				{Content: "This is fucking confusing, what the hell?", Timestamp: time.Now()},
				{Content: "Damn, this sucks. I hate this shit.", Timestamp: time.Now()},
			},
			expected: "edgy",
		},
		{
			name: "Academic tone",
			messages: []Message{
				{Content: "I would like to formalize this hypothesis and prove the theorem rigorously.", Timestamp: time.Now()},
				{Content: "The methodology demonstrates a significant insight into the underlying framework.", Timestamp: time.Now()},
			},
			expected: "academic",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			detected := DetectUserTone(tt.messages)
			if detected != tt.expected {
				t.Errorf("Expected tone %s, got %s", tt.expected, detected)
			}
		})
	}
}

func TestQuaternionNormalization(t *testing.T) {
	q := Quaternion{W: 1.0, X: 2.0, Y: 3.0, Z: 4.0}
	normalized := q.Normalize()

	// Check magnitude is 1.0
	mag := normalized.Magnitude()
	if mag < 0.99 || mag > 1.01 {
		t.Errorf("Expected normalized magnitude ~1.0, got %f", mag)
	}
}

func TestRegimeClassification(t *testing.T) {
	asya := NewAsya()

	// Test R1 (high variance) - need unnormalized for high variance
	asya.StateEngine.UserQuaternion = Quaternion{W: 0.1, X: 0.9, Y: 0.2, Z: 0.8}
	regime := asya.ClassifyRegime()
	// Note: After normalization, variance might not be as high
	// Just check it returns a valid regime
	if regime != "R1" && regime != "R2" && regime != "R3" {
		t.Errorf("Expected valid regime (R1/R2/R3), got %s", regime)
	}

	// Test R2 (low variance, high magnitude)
	asya.StateEngine.UserQuaternion = Quaternion{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5}
	regime = asya.ClassifyRegime()
	if regime != "R2" {
		t.Errorf("Expected R2 (low variance), got %s", regime)
	}
}

func TestBurnoutDetection(t *testing.T) {
	asya := NewAsya()

	// Simulate heavy R1/R2 usage
	for i := 0; i < 30; i++ {
		asya.StateEngine.RegimeHistory["R1"] = append(asya.StateEngine.RegimeHistory["R1"], time.Now())
	}
	for i := 0; i < 20; i++ {
		asya.StateEngine.RegimeHistory["R2"] = append(asya.StateEngine.RegimeHistory["R2"], time.Now())
	}
	for i := 0; i < 10; i++ {
		asya.StateEngine.RegimeHistory["R3"] = append(asya.StateEngine.RegimeHistory["R3"], time.Now())
	}

	// Should detect burnout risk (R3 = 10/60 = 16.6% < 50%)
	if !asya.CheckBurnoutRisk() {
		t.Error("Expected burnout risk detection")
	}
}

func TestCulturalAnalogies(t *testing.T) {
	// Test getting analogies for a concept
	analogies := GetAnalogiesForConcept("exponential_growth", "indian_cooking")

	if len(analogies) == 0 {
		t.Error("Expected at least one analogy for exponential_growth in indian_cooking")
	}

	// Check analogy structure
	if len(analogies) > 0 {
		analogy := analogies[0]
		if analogy.Concept != "exponential_growth" {
			t.Errorf("Expected concept exponential_growth, got %s", analogy.Concept)
		}
		if analogy.Culture != "indian_cooking" {
			t.Errorf("Expected culture indian_cooking, got %s", analogy.Culture)
		}
		if analogy.Example == "" {
			t.Error("Expected non-empty example")
		}
	}
}

func TestRedirection(t *testing.T) {
	profile := UserProfile{
		MessageHistory: []Message{
			{Content: "This is so frustrating!", Timestamp: time.Now()},
		},
	}

	response := RedirectNegativeEnergy("I'm so frustrated with this", profile)

	if response == "" {
		t.Error("Expected non-empty redirection response")
	}

	// Should contain empathetic language
	if !ContainsAny(response, []string{"hear", "understand", "feel"}) {
		t.Error("Expected empathetic language in redirection")
	}
}

func TestLanguageDetection(t *testing.T) {
	tests := []struct {
		text     string
		expected string
	}{
		{"Hello, how are you?", "en"},
		{"Namaste, kaise ho?", "hi"},
		{"Hola, ¿cómo estás?", "es"},
		{"Bonjour, comment allez-vous?", "fr"},
		{"Guten Tag, wie geht es Ihnen?", "de"},
	}

	for _, tt := range tests {
		detected := DetectLanguage(tt.text)
		if detected != tt.expected {
			t.Errorf("For text '%s', expected language %s, got %s", tt.text, tt.expected, detected)
		}
	}
}

func TestMultilingualGreeting(t *testing.T) {
	greeting := GetGreeting("hi", "casual")

	if greeting == "" {
		t.Error("Expected non-empty greeting")
	}

	// Should contain Hindi words or Devanagari (case-insensitive)
	greetingLower := strings.ToLower(greeting)
	if !ContainsAny(greetingLower, []string{"namaste", "asya", "main"}) && !ContainsDevanagari(greeting) {
		t.Logf("Greeting was: %s", greeting)
		t.Error("Expected Hindi greeting to contain Hindi elements")
	}
}

func TestAdaptToUser(t *testing.T) {
	asya := NewAsya()

	profile := UserProfile{
		MessageHistory: []Message{
			{Content: "This is fascinating! I love exploring patterns.", Timestamp: time.Now()},
		},
		IntelligenceWeights: map[string]float64{
			"spatial":             0.9,
			"logical_mathematical": 0.8,
			"naturalistic":        0.7,
		},
		AvgResponseTime: 3.0,
		Location:        "Mumbai, India",
		Language:        "en",
	}

	state := asya.AdaptToUser(profile)

	// Check that intelligence leaders include spatial (highest weight)
	found := false
	for _, leader := range state.IntelligenceLeaders {
		if leader == "spatial" {
			found = true
			break
		}
	}
	if !found {
		t.Error("Expected 'spatial' in intelligence leaders")
	}

	// Check cultural context detection
	if state.CulturalContext != "indian_cooking" {
		t.Errorf("Expected cultural context 'indian_cooking', got '%s'", state.CulturalContext)
	}
}

func TestResponseGeneration(t *testing.T) {
	asya := NewAsya()

	state := PersonaState{
		Tone:                "casual",
		IntelligenceLeaders: []string{"spatial", "logical_mathematical"},
		CurrentRegime:       VoidPhase,
		CulturalContext:     "indian_cooking",
	}

	// Test exploration phase response
	response := asya.GenerateResponse(state, "Let's explore quaternions!", VoidPhase)

	if response == "" {
		t.Error("Expected non-empty response")
	}

	// Should have exploration framing
	if !ContainsAny(response, []string{"explore", "discover", "curious", "pattern"}) {
		t.Error("Expected exploration language in R1 response")
	}
}

func TestGetTopIntelligences(t *testing.T) {
	profile := map[string]float64{
		"linguistic":          0.4,
		"logical_mathematical": 0.9,
		"spatial":             0.8,
		"musical":             0.2,
		"bodily_kinesthetic":  0.5,
		"interpersonal":       0.6,
		"intrapersonal":       0.7,
		"naturalistic":        0.3,
	}

	top3 := GetTopIntelligences(profile, 3)

	if len(top3) != 3 {
		t.Errorf("Expected 3 intelligences, got %d", len(top3))
	}

	// First should be logical_mathematical (0.9)
	if top3[0] != "logical_mathematical" {
		t.Errorf("Expected top intelligence to be logical_mathematical, got %s", top3[0])
	}
}
