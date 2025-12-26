// Package matching implements pattern matching and similarity scoring for Urban Lens
//
// Mathematical Foundation:
//   - Quaternion similarity on S³ (unit 3-sphere)
//   - Levenshtein distance with Vedic optimization
//   - Digital root pre-filtering (88.9% elimination)
//   - Williams batching: O(√n × log₂(n))
//
// Ported from: github.com/asymm_ananta/ananta/internal/learning
// Author: Zen Gardener (Wave 3 - Ship Swarm)
// Created: 2025-12-27
package matching

import (
	"crypto/sha256"
	"fmt"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/vqc"
)

// Pattern represents a matchable pattern with constraints
type Pattern struct {
	ID          string                 // Unique identifier
	Name        string                 // Human-readable name
	Template    string                 // Pattern template (may contain placeholders)
	Category    string                 // Pattern category (error_handling, crud, etc.)
	Language    string                 // Programming language (Go, TypeScript, etc.)
	Constraints []Constraint           // Matching constraints
	Confidence  float64                // Confidence score [0.0, 1.0]
	Frequency   int                    // Usage count (for ranking)
	Metadata    map[string]interface{} // Additional metadata
	State       vqc.Quaternion         // Quaternion state encoding
	Hash        string                 // Content hash for deduplication
	CreatedAt   time.Time
	UpdatedAt   time.Time
}

// Constraint represents a matching constraint
type Constraint struct {
	Type      ConstraintType // Type of constraint
	Field     string         // Field to constrain
	Operator  Operator       // Comparison operator
	Value     interface{}    // Expected value
	Weight    float64        // Weight in scoring [0.0, 1.0]
	Optional  bool           // Is this constraint optional?
}

// ConstraintType defines the type of constraint
type ConstraintType string

const (
	ConstraintTypeExact      ConstraintType = "exact"       // Exact match required
	ConstraintTypeFuzzy      ConstraintType = "fuzzy"       // Fuzzy match allowed
	ConstraintTypeRegex      ConstraintType = "regex"       // Regex pattern
	ConstraintTypeRange      ConstraintType = "range"       // Numeric range
	ConstraintTypeStructural ConstraintType = "structural"  // Structural similarity
	ConstraintTypeSemantic   ConstraintType = "semantic"    // Semantic similarity
)

// Operator defines comparison operators
type Operator string

const (
	OperatorEquals      Operator = "=="  // Equality
	OperatorNotEquals   Operator = "!="  // Inequality
	OperatorGreater     Operator = ">"   // Greater than
	OperatorLess        Operator = "<"   // Less than
	OperatorGreaterEq   Operator = ">="  // Greater or equal
	OperatorLessEq      Operator = "<="  // Less or equal
	OperatorContains    Operator = "~="  // Contains (substring)
	OperatorMatches     Operator = "=~"  // Matches (regex)
	OperatorSimilarTo   Operator = "≈"   // Similar to (fuzzy)
)

// Match represents a pattern match result
type Match struct {
	Pattern     *Pattern               // Matched pattern
	Score       float64                // Match score [0.0, 1.0]
	Bindings    map[string]interface{} // Variable bindings
	Context     MatchContext           // Match context
	Explanation string                 // Human-readable explanation
	Confidence  float64                // Confidence in match
	Rank        int                    // Rank among all matches (1 = best)
}

// MatchContext provides context for a match
type MatchContext struct {
	InputHash       string                 // Hash of input
	MatchedAt       time.Time              // When match occurred
	AlgorithmUsed   string                 // Algorithm used (exact, fuzzy, semantic)
	ComputeTimeNs   int64                  // Computation time in nanoseconds
	QuaternionState vqc.Quaternion         // Quaternion state at match time
	Metadata        map[string]interface{} // Additional context
}

// RankedMatch pairs a match with quality metrics
type RankedMatch struct {
	Match        *Match
	QualityScore float64 // Overall quality (confidence × frequency × genericity)
	Rank         int     // Rank position (1 = best)
}

// SimilarityMetrics captures detailed similarity scores
type SimilarityMetrics struct {
	StructuralSimilarity float64 // Levenshtein-based [0.0, 1.0]
	QuaternionSimilarity float64 // Quaternion dot product [0.0, 1.0]
	SemanticSimilarity   float64 // Semantic similarity [0.0, 1.0]
	DigitalRootMatch     bool    // Digital root pre-filter
	OverallSimilarity    float64 // Combined score [0.0, 1.0]
}

// MatcherConfig configures the matcher behavior
type MatcherConfig struct {
	// Thresholds
	MinSimilarity       float64 // Minimum similarity for match [0.0, 1.0]
	ExactMatchThreshold float64 // Threshold for exact match (default: 1.0)
	FuzzyMatchThreshold float64 // Threshold for fuzzy match (default: 0.85)

	// Optimization
	UseDigitalRootFilter bool   // Use digital root pre-filtering (88.9% speedup)
	UseWilliamsBatching  bool   // Use Williams batching for large sets
	MaxPatterns          int    // Maximum patterns to consider

	// Weights for combined similarity
	StructuralWeight float64 // Weight for structural similarity
	QuaternionWeight float64 // Weight for quaternion similarity
	SemanticWeight   float64 // Weight for semantic similarity

	// Performance
	ParallelThreshold int // Parallel processing threshold (default: 100)
	TimeoutMs         int // Timeout in milliseconds (0 = no timeout)
}

// DefaultMatcherConfig returns sensible defaults
func DefaultMatcherConfig() MatcherConfig {
	return MatcherConfig{
		MinSimilarity:        0.70,
		ExactMatchThreshold:  1.0,
		FuzzyMatchThreshold:  0.85,
		UseDigitalRootFilter: true,
		UseWilliamsBatching:  true,
		MaxPatterns:          10000,
		StructuralWeight:     0.40,
		QuaternionWeight:     0.40,
		SemanticWeight:       0.20,
		ParallelThreshold:    100,
		TimeoutMs:            5000,
	}
}

// Matcher is the interface for pattern matching
type Matcher interface {
	// Match finds all matching patterns for input
	Match(input interface{}, patterns []Pattern) ([]Match, error)

	// BestMatch finds the single best match
	BestMatch(input interface{}, patterns []Pattern) (*Match, error)

	// MatchWithContext matches with additional context
	MatchWithContext(input interface{}, patterns []Pattern, ctx MatchContext) ([]Match, error)

	// RankMatches ranks matches by quality
	RankMatches(matches []Match) []RankedMatch
}

// HashContent generates SHA-256 hash of content
func HashContent(content string) string {
	hash := sha256.Sum256([]byte(content))
	return fmt.Sprintf("%x", hash[:8]) // First 8 bytes (16 hex chars)
}

// NewPattern creates a new pattern with quaternion state
func NewPattern(id, name, template, category, language string) *Pattern {
	// Encode pattern to quaternion state
	state := EncodeToQuaternion(template)

	return &Pattern{
		ID:          id,
		Name:        name,
		Template:    template,
		Category:    category,
		Language:    language,
		Constraints: []Constraint{},
		Confidence:  0.5, // Initial confidence
		Frequency:   1,
		Metadata:    make(map[string]interface{}),
		State:       state,
		Hash:        HashContent(template),
		CreatedAt:   time.Now(),
		UpdatedAt:   time.Now(),
	}
}

// EncodeToQuaternion encodes a string to quaternion representation
// Uses statistical properties: mean, variance, skewness, kurtosis
func EncodeToQuaternion(s string) vqc.Quaternion {
	if len(s) == 0 {
		return vqc.NewQuaternion(1, 0, 0, 0)
	}

	// Compute statistical moments
	var sum, sum2, sum3, sum4 float64
	n := float64(len(s))

	for _, r := range s {
		x := float64(r)
		sum += x
		sum2 += x * x
		sum3 += x * x * x
		sum4 += x * x * x * x
	}

	mean := sum / n
	variance := (sum2 / n) - (mean * mean)

	// Normalize to [-1, 1] range
	w := mean / 127.5 - 1.0
	x := variance / 10000.0 // Normalize variance
	y := (sum3/n - 3.0*mean*variance - mean*mean*mean) / 100000.0
	z := (sum4/n - 4.0*mean*sum3/n + 6.0*mean*mean*sum2/n - 3.0*mean*mean*mean*mean) / 1000000.0

	return vqc.NewQuaternion(w, x, y, z).Normalize()
}

// AddConstraint adds a constraint to the pattern
func (p *Pattern) AddConstraint(constraint Constraint) {
	p.Constraints = append(p.Constraints, constraint)
	p.UpdatedAt = time.Now()
}

// UpdateFrequency increments the frequency counter
func (p *Pattern) UpdateFrequency() {
	p.Frequency++
	p.UpdatedAt = time.Now()
}

// UpdateConfidence updates the confidence score
func (p *Pattern) UpdateConfidence(newConfidence float64) {
	if newConfidence < 0.0 {
		newConfidence = 0.0
	}
	if newConfidence > 1.0 {
		newConfidence = 1.0
	}
	p.Confidence = newConfidence
	p.UpdatedAt = time.Now()
}
