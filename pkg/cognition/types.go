package cognition

import (
	"time"

	"github.com/asymmetrica/urbanlens/pkg/vqc"
	"github.com/google/uuid"
)

// ============================================================================
// CORE TYPES - Observable Cognition System
// ============================================================================
//
// ARCHITECTURE:
// - Real-time streaming of thought processes at Tesla 4.909 Hz (203.9ms)
// - Complete cognitive state capture (quaternions, connections, metrics)
// - Three-Regime dynamics observable in real-time
// - Intervention capability (steer reasoning mid-process)
// - Recording/replay for analysis
//
// MATHEMATICAL FOUNDATIONS:
// - Tesla Harmonic: 4.909 Hz = 203.9ms streaming interval
// - Digital Root Clustering: O(1) pattern recognition (0-9 clusters)
// - Harmonic Mean: Rigorous quality measurement
// - Three-Regime Dynamics: EXPLORATION (30%) → OPTIMIZATION (20%) → STABILIZATION (50%)
//
// ============================================================================

// EventType categorizes cognitive events
type EventType string

const (
	EventConceptFormed   EventType = "CONCEPT_FORMED"    // New concept created
	EventConnectionMade  EventType = "CONNECTION_MADE"   // Semantic link established
	EventRegimeShift     EventType = "REGIME_SHIFT"      // Transition between regimes
	EventPatternDetected EventType = "PATTERN_DETECTED"  // Repeating structure found
	EventDecisionPoint   EventType = "DECISION_POINT"    // Multiple paths available
	EventConvergence     EventType = "CONVERGENCE"       // Reasoning stabilizing
	EventDivergence      EventType = "DIVERGENCE"        // Exploring new directions
	EventThought         EventType = "THOUGHT"           // Internal monologue stream
	EventStateSnapshot   EventType = "STATE_SNAPSHOT"    // Complete state capture
)

// Regime represents cognitive operating mode
type Regime string

const (
	RegimeExploration    Regime = "EXPLORATION"    // 30% - Divergent thinking
	RegimeOptimization   Regime = "OPTIMIZATION"   // 20% - Gradient descent
	RegimeStabilization  Regime = "STABILIZATION"  // 50% - Convergence
)

// CognitionEvent represents a single observable moment
type CognitionEvent struct {
	SessionID     string            `json:"session_id"`
	Timestamp     time.Time         `json:"timestamp"`
	EventType     EventType         `json:"event_type"`
	Regime        Regime            `json:"regime"`
	CurrentState  *CognitiveState   `json:"current_state,omitempty"`
	Delta         *StateDelta       `json:"delta,omitempty"`
	Message       string            `json:"message"`
	Metadata      map[string]interface{} `json:"metadata,omitempty"`
}

// CognitiveState is complete internal state at one moment
type CognitiveState struct {
	// Core state
	ActiveConcepts      []*QuaternionConcept `json:"active_concepts"`
	ConnectionGraph     *ConnectionGraph      `json:"connection_graph"`
	WorkingMemory       []vqc.Quaternion      `json:"working_memory"`

	// Metrics
	Confidence          float64 `json:"confidence"`           // Overall reasoning confidence
	Coherence           float64 `json:"coherence"`            // How well concepts relate
	Entropy             float64 `json:"entropy"`              // Uncertainty level

	// Regime
	CurrentRegime       Regime  `json:"current_regime"`
	RegimeProgress      float64 `json:"regime_progress"`  // 0.0-1.0

	// Digital Root distribution
	ClusterDistribution map[uint8]int  `json:"cluster_distribution"` // Concepts per digital root (0-9)

	// Timestamp
	CapturedAt          time.Time `json:"captured_at"`
}

// StateDelta captures what changed between events
type StateDelta struct {
	NewConcepts         []*QuaternionConcept `json:"new_concepts,omitempty"`
	NewConnections      []*Connection         `json:"new_connections,omitempty"`
	RemovedConcepts     []uuid.UUID           `json:"removed_concepts,omitempty"`
	RemovedConnections  []string              `json:"removed_connections,omitempty"`
	ConfidenceChange    float64               `json:"confidence_change"`
	RegimeChange        *RegimeTransition     `json:"regime_change,omitempty"`
}

// RegimeTransition captures regime shift details
type RegimeTransition struct {
	From        Regime    `json:"from"`
	To          Regime    `json:"to"`
	Reason      string    `json:"reason"`
	Progress    float64   `json:"progress"` // Progress in new regime
	Timestamp   time.Time `json:"timestamp"`
}

// ConnectionGraph represents concept relationships
type ConnectionGraph struct {
	Nodes map[uuid.UUID]*ConceptNode `json:"nodes"`
	Edges []*Connection              `json:"edges"`
}

// ConceptNode represents a concept in the graph
type ConceptNode struct {
	ID             uuid.UUID        `json:"id"`
	Label          string           `json:"label"`
	Quaternion     vqc.Quaternion   `json:"quaternion"`
	DigitalRoot    uint8            `json:"digital_root"`
	Confidence     float64          `json:"confidence"`
	Regime         Regime           `json:"regime"`

	// Visualization properties
	X              float64          `json:"x"`     // Position for layout
	Y              float64          `json:"y"`
	Size           float64          `json:"size"`  // Based on importance
	Color          string           `json:"color"` // Based on digital root
}

// Connection represents semantic link between concepts
type Connection struct {
	ID          string    `json:"id"`
	Source      uuid.UUID `json:"source"`
	Target      uuid.UUID `json:"target"`
	Similarity  float64   `json:"similarity"` // Quaternion similarity
	Strength    float64   `json:"strength"`   // Connection strength
	Type        string    `json:"type"`       // "semantic", "temporal", "causal"
	CreatedAt   time.Time `json:"created_at"`
}

// ThoughtStream represents one observation session
type ThoughtStream struct {
	SessionID       string                  `json:"session_id"`
	StartTime       time.Time               `json:"start_time"`
	CurrentRegime   Regime                  `json:"current_regime"`
	EventChannel    chan *CognitionEvent    `json:"-"` // Not serialized
	Active          bool                    `json:"active"`

	// State tracking
	LastState       *CognitiveState         `json:"last_state,omitempty"`
	EventCount      int                     `json:"event_count"`

	// Recording
	Recording       bool                    `json:"recording"`
	RecordedEvents  []*CognitionEvent       `json:"-"` // Not serialized (use recorder)
}

// InterventionRequest allows external steering of reasoning
type InterventionRequest struct {
	SessionID      string    `json:"session_id"`
	TargetConcept  uuid.UUID `json:"target_concept"`  // Which concept to affect
	Action         string    `json:"action"`          // "amplify", "suppress", "redirect"
	Strength       float64   `json:"strength"`        // 0.0-1.0
	Direction      *vqc.Quaternion `json:"direction,omitempty"` // For "redirect"
	Reason         string    `json:"reason"`          // Why intervening
}

// Recording stores complete session
type Recording struct {
	ID              uuid.UUID         `json:"id"`
	SessionID       string            `json:"session_id"`
	StartTime       time.Time         `json:"start_time"`
	EndTime         time.Time         `json:"end_time"`
	Events          []*CognitionEvent `json:"events"`
	FinalState      *CognitiveState   `json:"final_state"`
	Metadata        map[string]interface{} `json:"metadata"`

	// Statistics
	TotalEvents     int               `json:"total_events"`
	ConceptsFormed  int               `json:"concepts_formed"`
	ConnectionsMade int               `json:"connections_made"`
	RegimeShifts    int               `json:"regime_shifts"`
	Duration        time.Duration     `json:"duration"`
}

// VisualizationData packages data for frontend
type VisualizationData struct {
	Graph              *ConceptGraph           `json:"graph"`
	Timeline           *RegimeTimeline         `json:"timeline"`
	Distribution       *DigitalRootDistribution `json:"distribution"`
	Metrics            *QualityMetrics         `json:"metrics"`
	GeneratedAt        time.Time               `json:"generated_at"`
}

// ConceptGraph for D3.js visualization
type ConceptGraph struct {
	Nodes []*ConceptNode `json:"nodes"`
	Edges []*Connection  `json:"edges"`
}

// RegimeTimeline for progress visualization
type RegimeTimeline struct {
	Sessions []*RegimeSession `json:"sessions"`
}

// RegimeSession represents time in a regime
type RegimeSession struct {
	Regime      Regime    `json:"regime"`
	StartTime   time.Time `json:"start_time"`
	EndTime     time.Time `json:"end_time"`
	Duration    float64   `json:"duration"` // seconds
	Progress    float64   `json:"progress"` // 0.0-1.0
}

// DigitalRootDistribution for cluster visualization
type DigitalRootDistribution struct {
	Clusters []*ClusterInfo `json:"clusters"`
}

// ClusterInfo details one digital root cluster
type ClusterInfo struct {
	DigitalRoot uint8    `json:"digital_root"`
	Count       int      `json:"count"`
	Percentage  float64  `json:"percentage"`
	TopConcepts []string `json:"top_concepts"` // Top 3 concept labels
}

// QualityMetrics for session assessment
type QualityMetrics struct {
	Correctness float64 `json:"correctness"` // > 99.99%
	Performance float64 `json:"performance"` // Events/sec
	Reliability float64 `json:"reliability"` // 1.0 - error_rate
	Synergy     float64 `json:"synergy"`     // Cascade amplification
	Elegance    float64 `json:"elegance"`    // Mathematical patterns

	// Unified score (harmonic mean)
	UnifiedScore float64 `json:"unified_score"`
}

// WSMessage is WebSocket message envelope
type WSMessage struct {
	Type      string      `json:"type"`       // "event", "subscribe", "intervene"
	SessionID string      `json:"session_id"`
	Data      interface{} `json:"data"`
	Timestamp time.Time   `json:"timestamp"`
}

// QuaternionConcept represents a concept encoded as quaternion
type QuaternionConcept struct {
	ID              uuid.UUID              `json:"id"`
	Quaternion      vqc.Quaternion         `json:"quaternion"`
	DigitalRoot     uint8                  `json:"digital_root"`
	EntityType      string                 `json:"entity_type"`
	SourceID        uuid.UUID              `json:"source_id"`
	SourceType      string                 `json:"source_type"`
	Regime          Regime                 `json:"regime"`
	Confidence      float64                `json:"confidence"`
	HarmonicWeight  float64                `json:"harmonic_weight"`
	Data            map[string]interface{} `json:"data"`
	HumanAnnotation string                 `json:"human_annotation"`
	CreatedAt       time.Time              `json:"created_at"`
}

// ============================================================================
// CONSTANTS - Tesla Harmonics
// ============================================================================

const (
	// Tesla harmonic frequency: 4.909 Hz
	TeslaBaseFrequencyHz = 4.909

	// Tesla interval: 203.9ms (1/4.909 Hz)
	TeslaHarmonicMs = 203.9
)
