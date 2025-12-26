package swarm

import (
	"time"
)

// FixResult represents result from a single agent fix attempt
// Used by spawner and convergence monitor for parallel hypothesis exploration
type FixResult struct {
	// Identification
	VariantID   int       // Which variant (1 to K)
	PatternName string    // Pattern used (e.g., "MissingImport", "UndefinedVariable")

	// Success metrics
	Success         bool   // Did fix compile?
	ErrorsBefore    int    // Error count before fix
	ErrorsAfter     int    // Error count after fix
	ErrorDelta      int    // ErrorsAfter - ErrorsBefore (negative = improvement)
	NewErrors       []string // New errors introduced (if any)
	FixedErrors     []string // Errors that disappeared
	CompilationTime time.Duration

	// Confidence and context
	Confidence      float64 // Pattern confidence (0-1)
	FilesModified   []string
	LinesChanged    int

	// Fix details
	FixDescription  string
	DiffPatch       string // Actual code changes
	CompilerOutput  string // Full compiler output for analysis
	AppliedAt       time.Time // When fix was applied
	WorkspaceDir    string // Isolated workspace directory
	CleanedUp       bool   // Whether temp dir was cleaned
}

// FiveTimbresBreakdown shows individual scores for each quality dimension
// Used for democratic scoring across 7 Citizens in Φ-Earth model
type FiveTimbresBreakdown struct {
	Correctness  float64 // Error reduction (0-1)
	Performance  float64 // Compilation time (0-1)
	Reliability  float64 // No new errors (0-1)
	Synergy      float64 // Contextual fit (0-1)
	Elegance     float64 // Code quality (0-1)
	HarmonicMean float64 // Overall quality score
}

// ScoredResult pairs a fix result with its quality score
type ScoredResult struct {
	Result       *FixResult
	QualityScore float64
	Scores       FiveTimbresBreakdown
}

// AggregatedResult contains selection decision and analysis
// Democratic superposition across parallel hypotheses
type AggregatedResult struct {
	BestResult      *FixResult
	BestScore       float64
	AllScores       []ScoredResult
	TotalCandidates int
	SuccessfulFixes int
	FailedFixes     int
	Recommendation  string // "apply", "reject_all", "need_review"
	Rationale       string
}

// FiveTimbresWeights controls importance of each timbre (default: equal)
type FiveTimbresWeights struct {
	Correctness float64 // default: 1.0
	Performance float64 // default: 1.0
	Reliability float64 // default: 1.0
	Synergy     float64 // default: 1.0
	Elegance    float64 // default: 1.0
}

// ValidationResult indicates if fix should be applied
type ValidationResult struct {
	Approved    bool
	Reason      string
	Suggestions []string // If rejected, what to try next
}

// HypothesisVariant represents one parallel hypothesis in swarm exploration
// This is the Urban Lens adaptation - hypotheses about user intent, data interpretation, etc.
type HypothesisVariant struct {
	ID          string      // Unique variant ID
	Strategy    string      // Exploration strategy (conservative, aggressive, hybrid)
	Confidence  float64     // Expected success probability [0.0, 1.0]
	Priority    int         // Execution priority (1=highest)
	Context     interface{} // Domain-specific context
}
