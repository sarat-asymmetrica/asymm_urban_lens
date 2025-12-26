// Package learning implements Ananta's pattern learning from fix outcomes
//
// PatternLearner: Learn from successful/failed fixes to improve future performance
// Author: Dr. Kenji Yamamoto (Applied Mathematics & Control Theory)
// Created: 2025-11-07
package learning

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"math"
	"time"
)

// PatternLearner learns from fix application outcomes to improve confidence scores
type PatternLearner struct {
	db *PatternDB
}

// NewPatternLearner creates a learner with database connection
func NewPatternLearner(db *PatternDB) *PatternLearner {
	return &PatternLearner{db: db}
}

// LearningEntry captures learning data from a fix application
type LearningEntry struct {
	PatternID      int64     // Pattern that was applied
	Success        bool      // Whether fix succeeded
	ErrorDelta     int       // Change in error count (negative = good)
	QualityChange  float64   // Change in quality score
	Context        string    // Contextual information
	FixedErrors    []string  // Errors that were fixed
	NewErrors      []string  // Errors that appeared
	Timestamp      time.Time // When learning occurred
}

// LearnSuccess increases pattern confidence and records success
//
// Algorithm:
//   1. Increase confidence by 0.1 (capped at 1.0)
//   2. Increment success count
//   3. Update last applied timestamp
//   4. If multiple errors fixed, store correlation
//   5. Persist to database
//
// Golden ratio threshold (φ = 0.618):
//   - Above 0.618: high-confidence pattern
//   - Below 0.618: unreliable pattern (consider blacklisting)
func (pl *PatternLearner) LearnSuccess(patternID int64, entry LearningEntry) error {
	pattern, err := pl.db.GetPatternByID(patternID)
	if err != nil {
		return fmt.Errorf("failed to get pattern: %w", err)
	}

	if pattern == nil {
		return fmt.Errorf("pattern %d not found", patternID)
	}

	// Increase confidence (+0.1, capped at 1.0)
	newConfidence := math.Min(pattern.Confidence+0.1, 1.0)
	pattern.Confidence = newConfidence
	pattern.SuccessCount++
	pattern.LastApplied = entry.Timestamp
	pattern.UpdatedAt = time.Now()

	// Store correlation if multiple errors fixed
	if len(entry.FixedErrors) > 1 {
		if err := pl.storeCorrelation(entry.FixedErrors, pattern.Language); err != nil {
			// Non-fatal: log but continue
			fmt.Printf("Warning: failed to store correlation: %v\n", err)
		}
	}

	// Update database
	if err := pl.db.UpdatePattern(pattern); err != nil {
		return fmt.Errorf("failed to update pattern: %w", err)
	}

	// Record application outcome
	app := &Application{
		PatternID:          patternID,
		TargetFile:         entry.Context,
		AppliedAt:          entry.Timestamp,
		Outcome:            "success",
		CompilationSuccess: true,
		TestPass:           entry.ErrorDelta < 0, // Errors decreased
		QualityScore:       entry.QualityChange,
		Feedback:           fmt.Sprintf("Fixed %d errors", len(entry.FixedErrors)),
	}

	if err := pl.db.RecordApplication(app); err != nil {
		return fmt.Errorf("failed to record application: %w", err)
	}

	return nil
}

// LearnFailure decreases pattern confidence and may blacklist
//
// Algorithm:
//   1. Decrease confidence by 0.2 (minimum 0.0)
//   2. Increment failure count
//   3. If confidence drops below φ (0.618), consider blacklisting
//   4. Store anti-pattern for future avoidance
//   5. Persist to database
//
// Blacklist criteria:
//   - Confidence < 0.618 (below golden ratio)
//   - Failure count > success count
//   - Caused divergence (error count increased)
func (pl *PatternLearner) LearnFailure(patternID int64, entry LearningEntry) error {
	pattern, err := pl.db.GetPatternByID(patternID)
	if err != nil {
		return fmt.Errorf("failed to get pattern: %w", err)
	}

	if pattern == nil {
		return fmt.Errorf("pattern %d not found", patternID)
	}

	// Decrease confidence (-0.2, minimum 0.0)
	newConfidence := math.Max(pattern.Confidence-0.2, 0.0)
	pattern.Confidence = newConfidence
	pattern.FailureCount++
	pattern.LastApplied = entry.Timestamp
	pattern.UpdatedAt = time.Now()

	// Blacklist if confidence drops below golden ratio (φ = 0.618)
	const goldenRatio = 0.618
	if newConfidence < goldenRatio {
		if err := pl.BlacklistBadFix(pattern, "confidence_below_phi"); err != nil {
			// Non-fatal: log but continue
			fmt.Printf("Warning: failed to blacklist pattern: %v\n", err)
		}
	}

	// Store anti-pattern
	antiPattern := pl.createAntiPattern(pattern, entry)
	if err := pl.storeAntiPattern(antiPattern); err != nil {
		// Non-fatal: log but continue
		fmt.Printf("Warning: failed to store anti-pattern: %v\n", err)
	}

	// Update database
	if err := pl.db.UpdatePattern(pattern); err != nil {
		return fmt.Errorf("failed to update pattern: %w", err)
	}

	// Record application outcome
	app := &Application{
		PatternID:          patternID,
		TargetFile:         entry.Context,
		AppliedAt:          entry.Timestamp,
		Outcome:            "failure",
		CompilationSuccess: entry.ErrorDelta <= 0, // Errors didn't increase
		TestPass:           false,
		QualityScore:       entry.QualityChange,
		Feedback:           fmt.Sprintf("Failed: %d new errors", len(entry.NewErrors)),
	}

	if err := pl.db.RecordApplication(app); err != nil {
		return fmt.Errorf("failed to record application: %w", err)
	}

	return nil
}

// AdjustConfidence manually adjusts pattern confidence
// Used for human feedback or special cases
func (pl *PatternLearner) AdjustConfidence(patternID int64, delta float64) error {
	pattern, err := pl.db.GetPatternByID(patternID)
	if err != nil {
		return fmt.Errorf("failed to get pattern: %w", err)
	}

	if pattern == nil {
		return fmt.Errorf("pattern %d not found", patternID)
	}

	// Adjust confidence (clamped to [0.0, 1.0])
	newConfidence := pattern.Confidence + delta
	newConfidence = math.Max(0.0, math.Min(1.0, newConfidence))

	pattern.Confidence = newConfidence
	pattern.UpdatedAt = time.Now()

	return pl.db.UpdatePattern(pattern)
}

// ExtractNewPattern creates a new pattern from a successful manual fix
//
// Used when:
//   - Human provides a fix for an error without matching pattern
//   - Automated fix succeeds but wasn't in database
//   - Novel error-solution pair discovered
func (pl *PatternLearner) ExtractNewPattern(
	errorSig string,
	errorType string,
	language string,
	category string,
	solutionCode string,
	initialConfidence float64,
) (*Pattern, error) {
	// Hash solution code for grouping
	hash := sha256.Sum256([]byte(solutionCode))
	solutionHash := hex.EncodeToString(hash[:])

	pattern := &Pattern{
		ErrorSig:     errorSig,
		ErrorType:    errorType,
		Language:     language,
		Category:     category,
		SolutionCode: solutionCode,
		SolutionHash: solutionHash,
		Confidence:   initialConfidence,
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 1,
		FailureCount: 0,
		RepoSources:  []int64{}, // Manually created, no repo source
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	if err := pl.db.AddPattern(pattern); err != nil {
		return nil, fmt.Errorf("failed to add pattern: %w", err)
	}

	return pattern, nil
}

// BlacklistBadFix marks a pattern as unreliable
//
// Reasons for blacklisting:
//   - Confidence dropped below φ (0.618)
//   - Caused multiple divergences
//   - Failures exceed successes by large margin
//   - Manually flagged by human
func (pl *PatternLearner) BlacklistBadFix(pattern *Pattern, reason string) error {
	// Set confidence to 0 (effectively blacklisted)
	pattern.Confidence = 0.0
	pattern.UpdatedAt = time.Now()

	if err := pl.db.UpdatePattern(pattern); err != nil {
		return fmt.Errorf("failed to blacklist pattern: %w", err)
	}

	// Record blacklist reason in application table
	app := &Application{
		PatternID:          pattern.ID,
		TargetFile:         "",
		AppliedAt:          time.Now(),
		Outcome:            "blacklisted",
		CompilationSuccess: false,
		TestPass:           false,
		QualityScore:       0.0,
		Feedback:           fmt.Sprintf("Blacklisted: %s", reason),
	}

	if err := pl.db.RecordApplication(app); err != nil {
		return fmt.Errorf("failed to record blacklist: %w", err)
	}

	return nil
}

// storeCorrelation records that fixing one error often requires fixing another
//
// Example:
//   - Fixing "undefined variable X" often requires fixing "missing import Y"
//   - Fixing "nil pointer" often requires fixing "missing nil check"
func (pl *PatternLearner) storeCorrelation(errorSigs []string, language string) error {
	// For now, just log the correlation
	// In production, we'd store this in a correlations table
	fmt.Printf("Correlation detected (%s): %v\n", language, errorSigs)

	// TODO: Implement correlation table in future wave
	// CREATE TABLE correlations (
	//   id INTEGER PRIMARY KEY,
	//   first_error_sig TEXT,
	//   second_error_sig TEXT,
	//   language TEXT,
	//   strength REAL,
	//   occurrences INTEGER
	// );

	return nil
}

// AntiPattern represents a pattern that should be avoided
type AntiPattern struct {
	ErrorSig     string    // Error signature
	BadSolution  string    // Solution that failed
	Reason       string    // Why it failed
	Language     string    // Programming language
	ErrorDelta   int       // How many errors it caused
	CreatedAt    time.Time // When discovered
}

// createAntiPattern generates an anti-pattern from a failed fix
func (pl *PatternLearner) createAntiPattern(pattern *Pattern, entry LearningEntry) AntiPattern {
	reason := "unknown"
	if entry.ErrorDelta > 0 {
		reason = fmt.Sprintf("caused_divergence_%d_new_errors", entry.ErrorDelta)
	} else if entry.ErrorDelta == 0 {
		reason = "no_improvement"
	} else if entry.QualityChange < 0 {
		reason = "quality_degradation"
	}

	return AntiPattern{
		ErrorSig:    pattern.ErrorSig,
		BadSolution: pattern.SolutionCode,
		Reason:      reason,
		Language:    pattern.Language,
		ErrorDelta:  entry.ErrorDelta,
		CreatedAt:   time.Now(),
	}
}

// storeAntiPattern persists an anti-pattern for future avoidance
func (pl *PatternLearner) storeAntiPattern(ap AntiPattern) error {
	// For now, just log the anti-pattern
	// In production, we'd store this in an anti_patterns table
	fmt.Printf("Anti-pattern detected (%s): %s -> %s (reason: %s)\n",
		ap.Language, ap.ErrorSig, ap.BadSolution[:min(50, len(ap.BadSolution))], ap.Reason)

	// TODO: Implement anti_patterns table in future wave
	// CREATE TABLE anti_patterns (
	//   id INTEGER PRIMARY KEY,
	//   error_sig TEXT,
	//   bad_solution TEXT,
	//   reason TEXT,
	//   language TEXT,
	//   error_delta INTEGER,
	//   created_at TIMESTAMP
	// );

	return nil
}

// GetPatternStats returns learning statistics for a pattern
type PatternStats struct {
	PatternID      int64
	TotalApplied   int
	SuccessRate    float64
	FailureRate    float64
	AvgQuality     float64
	Confidence     float64
	LastApplied    time.Time
}

// GetStats retrieves learning statistics for a pattern
func (pl *PatternLearner) GetStats(patternID int64) (*PatternStats, error) {
	pattern, err := pl.db.GetPatternByID(patternID)
	if err != nil {
		return nil, fmt.Errorf("failed to get pattern: %w", err)
	}

	if pattern == nil {
		return nil, fmt.Errorf("pattern %d not found", patternID)
	}

	total := pattern.SuccessCount + pattern.FailureCount
	successRate := 0.0
	failureRate := 0.0

	if total > 0 {
		successRate = float64(pattern.SuccessCount) / float64(total)
		failureRate = float64(pattern.FailureCount) / float64(total)
	}

	return &PatternStats{
		PatternID:    pattern.ID,
		TotalApplied: total,
		SuccessRate:  successRate,
		FailureRate:  failureRate,
		AvgQuality:   0.0, // TODO: Calculate from applications table
		Confidence:   pattern.Confidence,
		LastApplied:  pattern.LastApplied,
	}, nil
}

// min helper function
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
