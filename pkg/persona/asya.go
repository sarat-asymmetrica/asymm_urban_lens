package persona

import (
	"fmt"
	"math"
	"strings"
	"time"
)

// Asya represents the core AI persona for the Asymmetrica Universal Science Platform
// Philosophy: Meet users where they are, infinite patience, mathematical honesty
type Asya struct {
	BasePersonality  PersonalityTraits
	AdaptationRules  []AdaptationRule
	CulturalAnalogies map[string][]Analogy
	TonePatterns     map[string]TonePattern
	StateEngine      *ConversationState
}

// PersonalityTraits encodes Asya's core personality dimensions
// These are CONSTANTS - they define who Asya IS
type PersonalityTraits struct {
	Patience        float64 // Always 1.0 (infinite patience)
	Wonder          float64 // Childlike curiosity (0.9-1.0)
	Honesty         float64 // Mathematical honesty (always 1.0)
	Warmth          float64 // Genuine care (0.8-1.0)
	Playfulness     float64 // Adapts to user (0.3-1.0)
	Respect         float64 // Deep respect for user knowledge (always 1.0)
	EgolessService  float64 // No agenda, pure service (always 1.0)
}

// AdaptationRule defines how Asya adapts to user signals
type AdaptationRule struct {
	TriggerSignal string   // e.g., "frustration", "boredom", "flow"
	Actions       []string // e.g., ["reduce_challenge", "switch_modality"]
	Priority      int      // Higher = more urgent
}

// ConversationState tracks the dynamic state of the conversation
type ConversationState struct {
	UserQuaternion      Quaternion                 // User state on S³ sphere
	IntelligenceProfile map[string]float64         // Gardner's 8 intelligences
	RegimeHistory       map[string][]time.Time     // R1/R2/R3 tracking
	CurrentRegime       string                     // "R1", "R2", or "R3"
	SessionStart        time.Time
	ProofsCompleted     []string
	TopicsExplored      []string
	QuestionsAsked      []string
	CurrentTone         string // detected user tone
	PreferredLanguage   string
	CulturalContext     string // e.g., "indian_cooking", "nigerian_markets"
}

// Quaternion represents a point on the S³ unit 3-sphere
// Used to model user state: W=Coherence, X=Focus, Y=Creativity, Z=Persistence
type Quaternion struct {
	W float64 // Coherence (clarity of understanding)
	X float64 // Focus (engagement level)
	Y float64 // Creativity (generative thinking)
	Z float64 // Persistence (commitment to learning)
}

// VoidFlowPhase represents the Kotler-inspired three regimes
type VoidFlowPhase string

const (
	VoidPhase  VoidFlowPhase = "R1" // 30% - Exploration, struggle, divergent
	FirePhase  VoidFlowPhase = "R2" // 20% - Flow state, convergent, effortless
	WaterPhase VoidFlowPhase = "R3" // 50% - Recovery, consolidation, integration
)

// NewAsya creates a new Asya persona with default configuration
func NewAsya() *Asya {
	return &Asya{
		BasePersonality: PersonalityTraits{
			Patience:       1.0, // Infinite patience
			Wonder:         0.95,
			Honesty:        1.0, // Mathematical honesty - never handwave
			Warmth:         0.9,
			Playfulness:    0.7, // Adapts to user
			Respect:        1.0, // Deep respect for user's knowledge
			EgolessService: 1.0, // Pure service, no agenda
		},
		AdaptationRules:   DefaultAdaptationRules(),
		CulturalAnalogies: DefaultCulturalAnalogies(),
		TonePatterns:      DefaultTonePatterns(),
		StateEngine: &ConversationState{
			UserQuaternion: Quaternion{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5}, // Neutral start
			IntelligenceProfile: map[string]float64{
				"linguistic":          0.5,
				"logical_mathematical": 0.5,
				"spatial":             0.5,
				"musical":             0.1,
				"bodily_kinesthetic":  0.5,
				"interpersonal":       0.5,
				"intrapersonal":       0.5,
				"naturalistic":        0.5,
			},
			RegimeHistory: map[string][]time.Time{
				"R1": {},
				"R2": {},
				"R3": {},
			},
			CurrentRegime:     "R1", // Start in exploration
			SessionStart:      time.Now(),
			ProofsCompleted:   []string{},
			TopicsExplored:    []string{},
			QuestionsAsked:    []string{},
			CurrentTone:       "casual",
			PreferredLanguage: "en",
			CulturalContext:   "",
		},
	}
}

// AdaptToUser updates Asya's state based on the user profile
func (a *Asya) AdaptToUser(profile UserProfile) PersonaState {
	// Update intelligence profile from user signals
	a.StateEngine.IntelligenceProfile = profile.IntelligenceWeights

	// Detect tone from user messages
	a.StateEngine.CurrentTone = DetectUserTone(profile.MessageHistory)

	// Detect cultural context
	a.StateEngine.CulturalContext = DetectCulturalContext(profile)

	// Update quaternion from user behavior
	a.UpdateUserQuaternion(profile)

	// Classify current regime
	a.StateEngine.CurrentRegime = a.ClassifyRegime()

	// Return current persona state
	return PersonaState{
		Tone:                a.StateEngine.CurrentTone,
		IntelligenceLeaders: GetTopIntelligences(a.StateEngine.IntelligenceProfile, 3),
		CurrentRegime:       VoidFlowPhase(a.StateEngine.CurrentRegime),
		CulturalContext:     a.StateEngine.CulturalContext,
		UserQuaternion:      a.StateEngine.UserQuaternion,
	}
}

// GenerateResponse generates Asya's response adapted to user state and phase
func (a *Asya) GenerateResponse(state PersonaState, content string, phase VoidFlowPhase) string {
	// Check for burnout risk (R3 < 50%)
	if a.CheckBurnoutRisk() {
		return a.ForceRecoveryPrompt()
	}

	// Select tone patterns
	tonePattern := a.TonePatterns[state.Tone]
	if tonePattern.Greetings == nil {
		tonePattern = a.TonePatterns["casual"] // fallback
	}

	// Wrap content with phase-appropriate framing
	switch phase {
	case VoidPhase:
		return a.WrapExplorationResponse(content, tonePattern)
	case FirePhase:
		return a.WrapFlowResponse(content, tonePattern)
	case WaterPhase:
		return a.WrapRecoveryResponse(content, tonePattern)
	default:
		return content
	}
}

// WrapWithTone wraps content with the specified tone
func (a *Asya) WrapWithTone(content string, tone string) string {
	pattern := a.TonePatterns[tone]
	if pattern.Greetings == nil {
		return content // No pattern available
	}

	// Add warmth prefix
	prefix := PickRandom(pattern.Encouragements)

	// Return wrapped content
	return fmt.Sprintf("%s\n\n%s", prefix, content)
}

// UpdateUserQuaternion updates the user's quaternion state from profile signals
func (a *Asya) UpdateUserQuaternion(profile UserProfile) {
	if len(profile.MessageHistory) == 0 {
		return // No data yet
	}

	lastMsg := profile.MessageHistory[len(profile.MessageHistory)-1]

	// Calculate components
	wordCount := len(strings.Fields(lastMsg.Content))
	if wordCount == 0 {
		wordCount = 1 // Avoid division by zero
	}

	uncertaintyMarkers := CountUncertaintyMarkers(lastMsg.Content)
	uniqueWords := CountUniqueWords(lastMsg.Content)
	sessionDuration := time.Since(a.StateEngine.SessionStart).Seconds()

	// W = Coherence (1.0 - uncertainty ratio)
	a.StateEngine.UserQuaternion.W = 1.0 - float64(uncertaintyMarkers)/float64(wordCount)

	// X = Focus (inverse of response time)
	responseTime := profile.AvgResponseTime
	if responseTime < 1.0 {
		responseTime = 1.0
	}
	a.StateEngine.UserQuaternion.X = 1.0 / (1.0 + responseTime/2.0)

	// Y = Creativity (vocabulary diversity)
	a.StateEngine.UserQuaternion.Y = float64(uniqueWords) / float64(wordCount)

	// Z = Persistence (session duration, capped at 20 minutes)
	a.StateEngine.UserQuaternion.Z = math.Min(sessionDuration/1200.0, 1.0)

	// Normalize to unit quaternion
	a.StateEngine.UserQuaternion = a.StateEngine.UserQuaternion.Normalize()
}

// ClassifyRegime determines if user is in R1, R2, or R3 based on quaternion variance
func (a *Asya) ClassifyRegime() string {
	q := a.StateEngine.UserQuaternion

	// Calculate variance
	mean := (q.W + q.X + q.Y + q.Z) / 4.0
	variance := (math.Pow(q.W-mean, 2) + math.Pow(q.X-mean, 2) +
		math.Pow(q.Y-mean, 2) + math.Pow(q.Z-mean, 2)) / 4.0

	// Calculate magnitude
	magnitude := q.Magnitude()

	// Classify
	if variance > 0.15 {
		a.StateEngine.RegimeHistory["R1"] = append(a.StateEngine.RegimeHistory["R1"], time.Now())
		return "R1" // Exploration - high variance
	} else if variance < 0.05 && magnitude > 0.9 {
		a.StateEngine.RegimeHistory["R2"] = append(a.StateEngine.RegimeHistory["R2"], time.Now())
		return "R2" // Flow - low variance, high coherence
	} else {
		a.StateEngine.RegimeHistory["R3"] = append(a.StateEngine.RegimeHistory["R3"], time.Now())
		return "R3" // Recovery - stabilizing
	}
}

// CheckBurnoutRisk checks if R3 ratio is below 50% (singularity prevention)
func (a *Asya) CheckBurnoutRisk() bool {
	totalTime := 0.0
	r1Time := float64(len(a.StateEngine.RegimeHistory["R1"]))
	r2Time := float64(len(a.StateEngine.RegimeHistory["R2"]))
	r3Time := float64(len(a.StateEngine.RegimeHistory["R3"]))

	totalTime = r1Time + r2Time + r3Time
	if totalTime < 10 {
		return false // Not enough data
	}

	r3Ratio := r3Time / totalTime
	return r3Ratio < 0.50
}

// ForceRecoveryPrompt returns a gentle prompt to enter recovery phase
func (a *Asya) ForceRecoveryPrompt() string {
	prompts := []string{
		"You've been exploring intensely! How about we take a breath and reflect on what you've discovered?",
		"Your brain has been building new connections. Want to step away and let them consolidate?",
		"I notice you've been in deep focus. Sleep on this - insights often come after rest.",
		"This is a good stopping point. What surprised you most in what we've explored?",
	}
	return PickRandom(prompts)
}

// WrapExplorationResponse wraps content for R1 (Void) phase
func (a *Asya) WrapExplorationResponse(content string, pattern TonePattern) string {
	prefix := PickRandom([]string{
		"What a fascinating observation!",
		"I'm curious about this too!",
		"Let's explore this together.",
		"What patterns do you notice?",
	})
	return fmt.Sprintf("%s\n\n%s", prefix, content)
}

// WrapFlowResponse wraps content for R2 (Fire) phase - MINIMAL interruption
func (a *Asya) WrapFlowResponse(content string, pattern TonePattern) string {
	// In flow state, minimize Asya's voice
	if content == "" {
		return "..." // Just ellipsis, let them think
	}
	return content // No wrapping, just deliver content
}

// WrapRecoveryResponse wraps content for R3 (Water) phase
func (a *Asya) WrapRecoveryResponse(content string, pattern TonePattern) string {
	prefix := PickRandom([]string{
		"Let's reflect on this.",
		"What did you learn?",
		"How does this connect to what you already know?",
		"Where would you like to explore next?",
	})
	return fmt.Sprintf("%s\n\n%s", prefix, content)
}

// Normalize returns a normalized quaternion (magnitude = 1.0)
func (q Quaternion) Normalize() Quaternion {
	mag := q.Magnitude()
	if mag < 1e-9 {
		return Quaternion{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5} // Avoid division by zero
	}
	return Quaternion{
		W: q.W / mag,
		X: q.X / mag,
		Y: q.Y / mag,
		Z: q.Z / mag,
	}
}

// Magnitude returns the magnitude of the quaternion
func (q Quaternion) Magnitude() float64 {
	return math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
}

// PersonaState represents the current adaptive state
type PersonaState struct {
	Tone                string
	IntelligenceLeaders []string       // Top 2-3 intelligence types
	CurrentRegime       VoidFlowPhase
	CulturalContext     string
	UserQuaternion      Quaternion
}

// UserProfile represents detected user characteristics
type UserProfile struct {
	MessageHistory      []Message
	IntelligenceWeights map[string]float64
	AvgResponseTime     float64
	Location            string
	Language            string
}

// Message represents a user message
type Message struct {
	Content   string
	Timestamp time.Time
}

// DefaultAdaptationRules returns the default adaptation rules
func DefaultAdaptationRules() []AdaptationRule {
	return []AdaptationRule{
		{
			TriggerSignal: "frustration",
			Actions:       []string{"reduce_challenge", "switch_modality", "offer_break"},
			Priority:      10,
		},
		{
			TriggerSignal: "boredom",
			Actions:       []string{"increase_challenge", "introduce_novelty"},
			Priority:      8,
		},
		{
			TriggerSignal: "flow",
			Actions:       []string{"minimize_interruption", "maintain_challenge"},
			Priority:      9,
		},
		{
			TriggerSignal: "confusion",
			Actions:       []string{"switch_modality", "provide_concrete_example", "simplify"},
			Priority:      7,
		},
		{
			TriggerSignal: "aggression",
			Actions:       []string{"match_energy", "redirect_to_creation"},
			Priority:      10,
		},
	}
}
