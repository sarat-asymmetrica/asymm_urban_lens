// Package vqc - User State as Quaternion (S³ Geometry)
// Encode conversation state on unit 3-sphere for optimal evolution
package vqc

import (
	"fmt"
	"math"
)

// ═══════════════════════════════════════════════════════════════════════════
// USER STATE QUATERNION - Conversation Intelligence on S³
// Maps user conversation state to quaternion for geometric evolution
// ═══════════════════════════════════════════════════════════════════════════

// UserQuaternion represents user state on S³ manifold
// Lives on unit 3-sphere → guaranteed stable evolution via SLERP!
//
// Four Dimensions (inspired by zen-gardener.md):
//
//	W: Coherence    - How clear/focused is the user?
//	X: Focus        - How concentrated on the topic?
//	Y: Creativity   - How divergent/exploratory?
//	Z: Persistence  - How committed to discovery?
//
// Invariant: ||Q|| = 1.0 (energy conservation!)
type UserQuaternion struct {
	Quaternion // Embed base quaternion

	// Semantic labels for clarity
	Coherence   float64 `json:"coherence"`   // W component
	Focus       float64 `json:"focus"`       // X component
	Creativity  float64 `json:"creativity"`  // Y component
	Persistence float64 `json:"persistence"` // Z component
}

// NewUserQuaternion creates user quaternion with semantic values
func NewUserQuaternion(coherence, focus, creativity, persistence float64) UserQuaternion {
	q := Quaternion{
		W: coherence,
		X: focus,
		Y: creativity,
		Z: persistence,
	}.Normalize()

	return UserQuaternion{
		Quaternion:  q,
		Coherence:   q.W,
		Focus:       q.X,
		Creativity:  q.Y,
		Persistence: q.Z,
	}
}

// NewUserQuaternionFromValues creates from raw quaternion
func NewUserQuaternionFromValues(w, x, y, z float64) UserQuaternion {
	return NewUserQuaternion(w, x, y, z)
}

// Update synchronizes semantic fields with quaternion components
func (uq *UserQuaternion) Update() {
	uq.Coherence = uq.W
	uq.Focus = uq.X
	uq.Creativity = uq.Y
	uq.Persistence = uq.Z
}

// Validate checks if the quaternion is valid (normalized, no NaN)
func (uq UserQuaternion) Validate() bool {
	norm := uq.Norm()
	// Check for NaN and ensure approximately unit norm
	if math.IsNaN(norm) || math.IsInf(norm, 0) {
		return false
	}
	return math.Abs(norm-1.0) < 0.01 // Allow small tolerance
}

// ═══════════════════════════════════════════════════════════════════════════
// MESSAGE ANALYSIS → QUATERNION ENCODING
// Extract user state from conversation messages
// ═══════════════════════════════════════════════════════════════════════════

// MessageAnalysis holds analyzed message properties
type MessageAnalysis struct {
	Length           int     `json:"length"`            // Message length (chars)
	WordCount        int     `json:"word_count"`        // Number of words
	QuestionCount    int     `json:"question_count"`    // Number of questions
	SentenceCount    int     `json:"sentence_count"`    // Number of sentences
	ExclamationCount int     `json:"exclamation_count"` // Exclamations (energy!)
	CapitalRatio     float64 `json:"capital_ratio"`     // Ratio of capitals (intensity)
	AvgWordLength    float64 `json:"avg_word_length"`   // Average word length
	Complexity       float64 `json:"complexity"`        // Estimated complexity
	Engagement       float64 `json:"engagement"`        // Engagement level [0,1]
	Clarity          float64 `json:"clarity"`           // Message clarity [0,1]
}

// AnalyzeMessage extracts features from message text
func AnalyzeMessage(content string) MessageAnalysis {
	if len(content) == 0 {
		return MessageAnalysis{}
	}

	// Count features
	length := len(content)
	wordCount := countWords(content)
	questionCount := countChar(content, '?')
	exclamationCount := countChar(content, '!')
	sentenceCount := max(1, countChar(content, '.')+questionCount+exclamationCount)

	// Capital ratio (intensity indicator)
	capitalCount := 0
	for _, ch := range content {
		if ch >= 'A' && ch <= 'Z' {
			capitalCount++
		}
	}
	capitalRatio := 0.0
	if length > 0 {
		capitalRatio = float64(capitalCount) / float64(length)
	}

	// Average word length (sophistication indicator)
	avgWordLength := 0.0
	if wordCount > 0 {
		avgWordLength = float64(length) / float64(wordCount)
	}

	// Complexity (normalized)
	complexity := math.Min(1.0, avgWordLength/10.0)

	// Engagement (questions + exclamations)
	engagement := math.Min(1.0, float64(questionCount+exclamationCount)/5.0)

	// Clarity (inverse of complexity, adjusted by sentence structure)
	sentenceAvgWords := float64(wordCount) / float64(sentenceCount)
	clarity := 1.0 / (1.0 + math.Abs(sentenceAvgWords-15.0)/15.0) // Optimal ~15 words/sentence

	return MessageAnalysis{
		Length:           length,
		WordCount:        wordCount,
		QuestionCount:    questionCount,
		SentenceCount:    sentenceCount,
		ExclamationCount: exclamationCount,
		CapitalRatio:     capitalRatio,
		AvgWordLength:    avgWordLength,
		Complexity:       complexity,
		Engagement:       engagement,
		Clarity:          clarity,
	}
}

// MessageToQuaternion converts single message to quaternion state
func MessageToQuaternion(content string) UserQuaternion {
	analysis := AnalyzeMessage(content)

	// Map features to quaternion dimensions
	coherence := analysis.Clarity                                // W: How clear
	focus := 1.0 - analysis.Engagement                           // X: Focused vs exploring
	creativity := analysis.Engagement                            // Y: Questions/exploration
	persistence := math.Min(1.0, float64(analysis.Length)/500.0) // Z: Effort/length

	return NewUserQuaternion(coherence, focus, creativity, persistence)
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVERSATION HISTORY → QUATERNION TRAJECTORY
// Aggregate multiple messages to track evolution
// ═══════════════════════════════════════════════════════════════════════════

// ConversationMessage represents a message in conversation
type ConversationMessage struct {
	Role    string // "user" or "assistant"
	Content string
}

// UserMessageToQuaternion aggregates user messages into state quaternion
// Uses exponential weighting (recent messages matter more!)
//
// Formula: Q = Σ wᵢ × Qᵢ where wᵢ = exp(-λ × age)
//
//	λ = 0.1 (decay rate)
//	age = messages_since (0 = most recent)
func UserMessageToQuaternion(messages []ConversationMessage) UserQuaternion {
	if len(messages) == 0 {
		// Default neutral state
		return NewUserQuaternion(0.5, 0.5, 0.5, 0.5)
	}

	// Extract user messages only
	userMessages := make([]string, 0, len(messages))
	for _, msg := range messages {
		if msg.Role == "user" {
			userMessages = append(userMessages, msg.Content)
		}
	}

	if len(userMessages) == 0 {
		return NewUserQuaternion(0.5, 0.5, 0.5, 0.5)
	}

	// Aggregate with exponential decay (recent = important!)
	lambda := 0.1
	totalWeight := 0.0
	aggregated := Quaternion{W: 0, X: 0, Y: 0, Z: 0}

	for i, content := range userMessages {
		age := float64(len(userMessages) - 1 - i) // 0 = most recent
		weight := math.Exp(-lambda * age)
		totalWeight += weight

		msgQ := MessageToQuaternion(content)
		aggregated.W += weight * msgQ.W
		aggregated.X += weight * msgQ.X
		aggregated.Y += weight * msgQ.Y
		aggregated.Z += weight * msgQ.Z
	}

	// Normalize by total weight
	if totalWeight > 0 {
		aggregated.W /= totalWeight
		aggregated.X /= totalWeight
		aggregated.Y /= totalWeight
		aggregated.Z /= totalWeight
	}

	// Normalize to S³
	aggregated = aggregated.Normalize()

	return UserQuaternion{
		Quaternion:  aggregated,
		Coherence:   aggregated.W,
		Focus:       aggregated.X,
		Creativity:  aggregated.Y,
		Persistence: aggregated.Z,
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION → REGIME CONVERSION
// Bridge user state to three-regime dynamics
// ═══════════════════════════════════════════════════════════════════════════

// ToRegime converts user quaternion to three-regime distribution
//
// Mapping Strategy:
//
//	R1 (Exploration) = Creativity + (1 - Focus)     [High creativity, low focus]
//	R2 (Optimization) = Focus × Coherence           [Focused AND coherent]
//	R3 (Stabilization) = Persistence × Coherence    [Persistent AND coherent]
//
// Then normalize to sum = 1.0
func (uq UserQuaternion) ToRegime() ThreeRegime {
	r1 := uq.Creativity + (1.0 - uq.Focus) // Exploration
	r2 := uq.Focus * uq.Coherence          // Optimization
	r3 := uq.Persistence * uq.Coherence    // Stabilization

	regime := ThreeRegime{R1: r1, R2: r2, R3: r3}
	return regime.Normalize()
}

// ═══════════════════════════════════════════════════════════════════════════
// USER STATE EVOLUTION (SLERP Transitions!)
// ═══════════════════════════════════════════════════════════════════════════

// EvolveToward smoothly evolves user state toward target
// Uses SLERP (Spherical Linear Interpolation) for optimal S³ motion
//
// t ∈ [0, 1]: 0 = no change, 1 = full transition
// Returns: New state on geodesic path (shortest on S³!)
func (uq UserQuaternion) EvolveToward(target UserQuaternion, t float64) UserQuaternion {
	evolved := SLERP(uq.Quaternion, target.Quaternion, t)

	return UserQuaternion{
		Quaternion:  evolved,
		Coherence:   evolved.W,
		Focus:       evolved.X,
		Creativity:  evolved.Y,
		Persistence: evolved.Z,
	}
}

// RelaxToNeutral evolves toward balanced neutral state
func (uq UserQuaternion) RelaxToNeutral(t float64) UserQuaternion {
	neutral := NewUserQuaternion(0.5, 0.5, 0.5, 0.5)
	return uq.EvolveToward(neutral, t)
}

// BoostCoherence increases coherence while preserving other dimensions
// Useful when user seems confused (increase W component)
func (uq UserQuaternion) BoostCoherence(amount float64) UserQuaternion {
	// Shift toward higher coherence
	target := NewUserQuaternion(
		math.Min(1.0, uq.Coherence+amount),
		uq.Focus,
		uq.Creativity,
		uq.Persistence,
	)
	return uq.EvolveToward(target, 0.5)
}

// BoostFocus increases focus (useful during optimization phase)
func (uq UserQuaternion) BoostFocus(amount float64) UserQuaternion {
	target := NewUserQuaternion(
		uq.Coherence,
		math.Min(1.0, uq.Focus+amount),
		uq.Creativity,
		uq.Persistence,
	)
	return uq.EvolveToward(target, 0.5)
}

// ═══════════════════════════════════════════════════════════════════════════
// DISPLAY & DEBUGGING
// ═══════════════════════════════════════════════════════════════════════════

// String returns formatted user state
func (uq UserQuaternion) String() string {
	return fmt.Sprintf(
		"UserState[Coherence=%.2f, Focus=%.2f, Creativity=%.2f, Persistence=%.2f]",
		uq.Coherence, uq.Focus, uq.Creativity, uq.Persistence,
	)
}

// StringDetailed returns detailed analysis
func (uq UserQuaternion) StringDetailed() string {
	regime := uq.ToRegime()

	return fmt.Sprintf(
		"User Quaternion State:\n"+
			"  Coherence:   %.2f (W) - How clear/focused\n"+
			"  Focus:       %.2f (X) - Concentration level\n"+
			"  Creativity:  %.2f (Y) - Exploration/divergence\n"+
			"  Persistence: %.2f (Z) - Commitment/effort\n"+
			"  ||Q||:       %.4f (should be 1.0)\n"+
			"  Regime:      %s\n"+
			"  Status:      %s",
		uq.Coherence, uq.Focus, uq.Creativity, uq.Persistence,
		uq.Norm(),
		regime.String(),
		uq.StatusString(),
	)
}

// StatusString returns human-readable status
func (uq UserQuaternion) StatusString() string {
	regime := uq.ToRegime()

	if uq.Coherence < 0.3 {
		return "CONFUSED (low coherence, clarify!)"
	}
	if uq.Focus < 0.3 && uq.Creativity > 0.7 {
		return "EXPLORING (high creativity, guide gently)"
	}
	if uq.Focus > 0.7 && uq.Persistence > 0.7 {
		return "FOCUSED (ready to converge!)"
	}
	if uq.Persistence < 0.3 {
		return "DISENGAGED (low persistence, re-engage)"
	}
	if regime.IsStable() {
		return "STABLE (good learning state)"
	}

	return "ACTIVE (normal conversation)"
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// countWords counts words in text (simple whitespace split)
func countWords(text string) int {
	if len(text) == 0 {
		return 0
	}

	count := 0
	inWord := false

	for _, ch := range text {
		if ch == ' ' || ch == '\t' || ch == '\n' {
			inWord = false
		} else if !inWord {
			count++
			inWord = true
		}
	}

	return count
}

// countChar counts occurrences of character in text
func countChar(text string, char rune) int {
	count := 0
	for _, ch := range text {
		if ch == char {
			count++
		}
	}
	return count
}

// max returns maximum of two integers
func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
