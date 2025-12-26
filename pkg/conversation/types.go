// Package conversation - The Universal Science Discovery Engine
// Implements the Sarat Method + Void-Flow-Solution Framework
// Enables anyone to go from observation → formalized theorem
package conversation

import (
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONVERSATION STATE MACHINE
// ═══════════════════════════════════════════════════════════════════════════

// ConversationState represents where we are in the Sarat Method flow
type ConversationState string

const (
	StateGreeting     ConversationState = "GREETING"      // Initial contact, language detection
	StateAnchoring    ConversationState = "ANCHORING"     // Get concrete, sensory observation
	StateWhyChaining  ConversationState = "WHY_CHAINING"  // Ask "why" 5+ times, go deep
	StateSynthesizing ConversationState = "SYNTHESIZING"  // Connect to existing knowledge
	StateFormalizing  ConversationState = "FORMALIZING"   // Introduce Lean, create theorem
	StateCelebrating  ConversationState = "CELEBRATING"   // Honor the discovery
	StateStuck        ConversationState = "STUCK"         // User needs help
)

// VoidFlowPhase represents the three-regime dynamics
type VoidFlowPhase string

const (
	PhaseVoid     VoidFlowPhase = "VOID"     // 30% - High D exploration
	PhaseFlow     VoidFlowPhase = "FLOW"     // 20% - Exponential convergence
	PhaseSolution VoidFlowPhase = "SOLUTION" // 50% - Stable attractor
)

// IntelligenceType represents Gardner's 8 intelligences
type IntelligenceType string

const (
	IntKinesthetic IntelligenceType = "KINESTHETIC" // Body, touch, movement
	IntVisual      IntelligenceType = "VISUAL"      // Sight, color, spatial
	IntAuditory    IntelligenceType = "AUDITORY"    // Sound, rhythm, music
	IntSpatial     IntelligenceType = "SPATIAL"     // Patterns, maps, shapes
	IntLogical     IntelligenceType = "LOGICAL"     // Numbers, systems, logic
	IntLinguistic  IntelligenceType = "LINGUISTIC"  // Words, stories, metaphor
	IntSocial      IntelligenceType = "SOCIAL"      // People, empathy, group dynamics
	IntNaturalist  IntelligenceType = "NATURALIST"  // Nature, patterns, classification
	IntUnknown     IntelligenceType = "UNKNOWN"     // Not yet determined
)

// ═══════════════════════════════════════════════════════════════════════════
// CORE TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Conversation tracks the full conversation state
type Conversation struct {
	ID            string            `json:"id"`
	UserID        string            `json:"user_id,omitempty"`
	State         ConversationState `json:"state"`
	Phase         VoidFlowPhase     `json:"phase"`
	Profile       UserProfile       `json:"profile"`
	Messages      []Message         `json:"messages"`
	WhyChainDepth int               `json:"why_chain_depth"`
	Anchor        string            `json:"anchor"` // The concrete observation
	Insights      []Insight         `json:"insights"`
	LeanTheorem   string            `json:"lean_theorem,omitempty"`
	CreatedAt     time.Time         `json:"created_at"`
	LastMessageAt time.Time         `json:"last_message_at"`
	Metadata      map[string]any    `json:"metadata,omitempty"`
}

// UserProfile tracks user characteristics (adaptive learning)
type UserProfile struct {
	Language               string                      `json:"language"` // Detected language (ISO 639-1)
	IntelligenceProfile    map[IntelligenceType]float64 `json:"intelligence_profile"`
	DominantIntelligence   IntelligenceType            `json:"dominant_intelligence"`
	SophisticationLevel    int                         `json:"sophistication_level"` // 1-10 (child → PhD)
	ConversationPace       string                      `json:"conversation_pace"`    // slow, medium, fast
	PreferredAnalogyDomain []string                    `json:"preferred_analogy_domain"`
	TonePreference         string                      `json:"tone_preference"` // formal, casual, playful
	CulturalContext        string                      `json:"cultural_context,omitempty"`
}

// Message represents one message in conversation
type Message struct {
	ID        string            `json:"id"`
	Role      string            `json:"role"` // user, assistant
	Content   string            `json:"content"`
	Timestamp time.Time         `json:"timestamp"`
	State     ConversationState `json:"state"` // State when sent
	Phase     VoidFlowPhase     `json:"phase"` // Phase when sent
	Metadata  map[string]any    `json:"metadata,omitempty"`
}

// Insight represents a discovered insight during the conversation
type Insight struct {
	Description string   `json:"description"`
	Domain      string   `json:"domain"`      // cooking, business, physics, etc.
	Connections []string `json:"connections"` // Other domains it connects to
	WhyDepth    int      `json:"why_depth"`   // How deep the chain went
	Timestamp   time.Time `json:"timestamp"`
}

// Entity represents an entity extracted from conversation
// (Used for knowledge graph building in future)
type Entity struct {
	Name       string   `json:"name"`
	Type       string   `json:"type"`       // object, concept, person, process
	Attributes []string `json:"attributes"` // Properties mentioned
	Relations  []string `json:"relations"`  // Relationships to other entities
}

// Constraint represents a constraint discovered
type Constraint struct {
	Description string `json:"description"`
	Type        string `json:"type"` // physical, logical, temporal, etc.
	Source      string `json:"source"`
}

// Discovery represents a major "aha!" moment
type Discovery struct {
	Insight       string    `json:"insight"`
	MechanismType string    `json:"mechanism_type"` // thermodynamic, kinetic, quantum, etc.
	Formalization string    `json:"formalization"`  // The Lean code
	Timestamp     time.Time `json:"timestamp"`
}

// ═══════════════════════════════════════════════════════════════════════════
// INTERFACES (Dependency injection for testability)
// ═══════════════════════════════════════════════════════════════════════════

// AIClient interface for LLM integration (OpenAI, Anthropic, etc.)
type AIClient interface {
	// GenerateResponse generates AI response given conversation context
	GenerateResponse(conv *Conversation, systemPrompt, userMessage string) (string, error)
}

// LeanBridge interface for Lean theorem prover integration
type LeanBridge interface {
	// GenerateTheorem creates Lean code from conversation insights
	GenerateTheorem(conv *Conversation) (string, error)

	// ValidateTheorem checks if Lean code compiles
	ValidateTheorem(leanCode string) (bool, error)
}

// KnowledgeGraph interface for knowledge base integration
type KnowledgeGraph interface {
	// FindRelatedConcepts finds concepts related to the current insight
	FindRelatedConcepts(domain string, concept string) ([]string, error)

	// StoreInsight saves an insight to the knowledge graph
	StoreInsight(insight Insight) error
}

// LanguageDetector interface for language detection
type LanguageDetector interface {
	// Detect returns ISO 639-1 language code
	Detect(text string) (string, error)
}

// ═══════════════════════════════════════════════════════════════════════════
// PROMPT TEMPLATES
// ═══════════════════════════════════════════════════════════════════════════

// PromptTemplate represents a localized prompt template
type PromptTemplate struct {
	Language           string `json:"language"`
	IntelligenceType   IntelligenceType `json:"intelligence_type,omitempty"`
	TemplateText       string `json:"template_text"`
	ExampleResponse    string `json:"example_response,omitempty"`
}

// ConversationStyle adapts conversation to user's intelligence type
type ConversationStyle struct {
	PreferAnalogies    bool   `json:"prefer_analogies"`
	PreferDiagrams     bool   `json:"prefer_diagrams"`
	PreferPatterns     bool   `json:"prefer_patterns"`
	PreferFormalism    bool   `json:"prefer_formalism"`
	PreferStories      bool   `json:"prefer_stories"`
	AnalogyDomain      string `json:"analogy_domain,omitempty"`
	LeanIntroduction   string `json:"lean_introduction"`
	PaceGoal           string `json:"pace_goal"` // slow, medium, fast
}

// PhaseStrategy defines strategy for each Void-Flow-Solution phase
type PhaseStrategy struct {
	Goal          string `json:"goal"`
	PromptStyle   string `json:"prompt_style"`
	PaceGoal      string `json:"pace_goal"`
	NextStateGoal string `json:"next_state_goal"`
}

// WhyStep represents one step in the why-chain
type WhyStep struct {
	Question string `json:"question"`
	Answer   string `json:"answer"`
	Depth    int    `json:"depth"`
}
