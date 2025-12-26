// Package learning implements feedback-driven confidence updates
//
// Feedback: Application outcome tracking and confidence adjustment
// Author: Agent 1.3 (Dr. Chen Wei)
// Created: 2025-11-07
package learning

import (
	"fmt"
	"math"
	"time"
)

// OutcomeType represents the result of applying a pattern
type OutcomeType string

const (
	OutcomeSuccess  OutcomeType = "success"  // Pattern fixed the error successfully
	OutcomeFailure  OutcomeType = "failure"  // Pattern failed to fix (compilation/test failure)
	OutcomeRejected OutcomeType = "rejected" // Pattern not applied (user rejected, context mismatch)
)

// ApplicationOutcome tracks the result of applying a pattern to fix an error
//
// This is the reward signal for reinforcement learning:
// - Outcome: success/failure/rejected (discrete reward)
// - CompilationSuccess: did code compile after fix? (binary signal)
// - TestPass: did tests pass after fix? (binary signal)
// - QualityScore: Five Timbres harmonic mean (continuous signal, 0.0-1.0)
type ApplicationOutcome struct {
	PatternID          int64       // Which pattern was applied
	TargetFile         string      // File that was modified
	AppliedAt          time.Time   // When pattern was applied
	Outcome            OutcomeType // success/failure/rejected
	CompilationSuccess bool        // Did compilation succeed?
	TestPass           bool        // Did tests pass?
	QualityScore       float64     // Harmonic mean (Five Timbres: 0.0-1.0)
	Feedback           string      // Human or automated feedback text
}

// RecordApplication stores application outcome in database
//
// This creates the experience replay buffer for learning:
// - Every application is logged (success AND failure)
// - Enables temporal analysis (pattern performance over time)
// - Supports offline learning (batch updates from historical data)
//
// Example:
//
//	outcome := ApplicationOutcome{
//	    PatternID: 42,
//	    TargetFile: "main.go",
//	    Outcome: OutcomeSuccess,
//	    CompilationSuccess: true,
//	    TestPass: true,
//	    QualityScore: 0.92,
//	    Feedback: "Fixed nil pointer, all tests pass",
//	}
//	err := RecordApplication(db, outcome)
func RecordApplication(db *PatternDB, outcome ApplicationOutcome) error {
	app := &Application{
		PatternID:          outcome.PatternID,
		TargetFile:         outcome.TargetFile,
		AppliedAt:          outcome.AppliedAt,
		Outcome:            string(outcome.Outcome),
		CompilationSuccess: outcome.CompilationSuccess,
		TestPass:           outcome.TestPass,
		QualityScore:       outcome.QualityScore,
		Feedback:           outcome.Feedback,
	}

	if err := db.RecordApplication(app); err != nil {
		return fmt.Errorf("failed to record application: %w", err)
	}

	return nil
}

// UpdateConfidenceFromOutcome adjusts pattern confidence based on outcome
//
// Reinforcement learning update:
//
//	Q(s,a) ← Q(s,a) + α[r + γ max Q(s',a') - Q(s,a)]
//
// Simplified for our case (no future states):
//
//	confidence_new = confidence_old + α × reward
//
// Where:
//   - α = learning rate (0.05 for success, 0.10 for failure - asymmetric)
//   - reward = +1 for success, -1 for failure, 0 for rejected
//
// Asymmetric learning:
// - Slower to trust (α=0.05 for positive updates)
// - Faster to distrust (α=0.10 for negative updates)
// - This makes the system cautious (conservative Bayesian prior)
//
// Bounds:
// - Confidence clamped to [0.10, 0.99]
// - Never fully 0 (always some exploration chance)
// - Never fully 1 (always some uncertainty)
//
// Example:
//
//	// Pattern at 0.75 confidence, applied successfully
//	err := UpdateConfidenceFromOutcome(db, 42, OutcomeSuccess)
//	// New confidence: 0.75 + 0.05 = 0.80 (promoted to HIGH tier!)
func UpdateConfidenceFromOutcome(
	db *PatternDB,
	patternID int64,
	outcome OutcomeType,
) error {
	// Get current confidence
	query := `SELECT confidence FROM patterns WHERE id = ?`
	var currentConfidence float64
	err := db.db.QueryRow(query, patternID).Scan(&currentConfidence)
	if err != nil {
		return fmt.Errorf("failed to get current confidence: %w", err)
	}

	// Calculate confidence update
	var newConfidence float64
	switch outcome {
	case OutcomeSuccess:
		// Reward signal: +0.05 (conservative increase)
		newConfidence = currentConfidence + 0.05
		// Cap at 0.99 (never fully certain)
		newConfidence = math.Min(newConfidence, 0.99)

	case OutcomeFailure:
		// Penalty signal: -0.10 (aggressive decrease)
		newConfidence = currentConfidence - 0.10
		// Floor at 0.10 (never fully abandon, always keep exploration chance)
		newConfidence = math.Max(newConfidence, 0.10)

	case OutcomeRejected:
		// No change - pattern wasn't actually applied
		newConfidence = currentConfidence
	}

	// Update confidence in database
	if err := db.UpdatePatternConfidence(patternID, newConfidence); err != nil {
		return fmt.Errorf("failed to update confidence: %w", err)
	}

	return nil
}

// CalculateQualityScore computes Five Timbres harmonic mean
//
// Five dimensions (each 0.0-1.0):
// 1. Correctness: Did it fix the error? (compilation + tests)
// 2. Performance: No regressions? (still meets timing constraints)
// 3. Reliability: Handles edge cases? (doesn't introduce new errors)
// 4. Synergy: Composes well? (fits codebase patterns)
// 5. Elegance: Clean code? (readable, maintainable)
//
// Harmonic mean formula:
//
//	H = n / (1/x₁ + 1/x₂ + ... + 1/xₙ)
//
// Why harmonic mean?
// - Penalizes weak dimensions (can't hide poor performance)
// - Example: [0.9, 0.9, 0.9, 0.9, 0.3] → harmonic = 0.51 (FAIL!)
// - Arithmetic mean would give 0.78 (misleadingly passing)
//
// This enforces D3-Enterprise Grade+ standards:
// - All dimensions must be strong (no weak links)
// - Quality is the minimum viable across all concerns
// - Aligns with "unified whole" philosophy
//
// Example:
//
//	scores := []float64{0.95, 0.90, 0.88, 0.92, 0.85}
//	quality := CalculateQualityScore(scores)
//	// quality ≈ 0.90 (all dimensions strong → high score)
func CalculateQualityScore(scores []float64) float64 {
	if len(scores) == 0 {
		return 0.0
	}

	// Harmonic mean: n / Σ(1/xᵢ)
	reciprocalSum := 0.0
	for _, score := range scores {
		if score > 0 {
			reciprocalSum += 1.0 / score
		}
	}

	if reciprocalSum == 0 {
		return 0.0
	}

	harmonicMean := float64(len(scores)) / reciprocalSum
	return harmonicMean
}

// GetSuccessRate retrieves success rate for a pattern
//
// Empirical success rate:
//
//	P(success) = successes / (successes + failures)
//
// Uses Laplace smoothing to handle small sample sizes:
//
//	P(success) = (successes + 1) / (successes + failures + 2)
//
// This prevents:
// - Division by zero
// - 100% success from single success (overconfidence)
// - 0% success from single failure (over-pessimism)
//
// Example:
//
//	rate, err := GetSuccessRate(db, 42)
//	// rate = 0.85 means pattern succeeds 85% of the time
func GetSuccessRate(db *PatternDB, patternID int64) (float64, error) {
	query := `SELECT success_count, failure_count FROM patterns WHERE id = ?`
	var successes, failures int
	err := db.db.QueryRow(query, patternID).Scan(&successes, &failures)
	if err != nil {
		return 0.0, fmt.Errorf("failed to get success rate: %w", err)
	}

	// Laplace smoothing (add 1 to numerator, 2 to denominator)
	successRate := float64(successes+1) / float64(successes+failures+2)
	return successRate, nil
}
