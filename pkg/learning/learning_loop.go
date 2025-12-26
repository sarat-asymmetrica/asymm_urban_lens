// Package learning implements Ananta's continuous learning loop
//
// Learning Loop: Adaptive confidence updates via feedback, decay, and human input
// Author: Agent 1.3 (Dr. Chen Wei - Reinforcement Learning Expert)
// Created: 2025-11-07
package learning

import (
	"context"
	"fmt"
	"time"
)

// LearningLoop orchestrates continuous learning for pattern confidence
//
// Three mechanisms:
// 1. Feedback processing: Success/failure outcomes adjust confidence
// 2. Temporal decay: Unused patterns lose confidence over time
// 3. Human input: Expert-verified patterns start with high confidence
//
// This is an online learning system inspired by:
// - Multi-armed bandit algorithms (exploration vs exploitation)
// - Temporal difference learning (confidence as value function)
// - Experience replay (storing and learning from outcomes)
type LearningLoop struct {
	db            *PatternDB
	decayInterval time.Duration // How often to run decay (default: 7 days)
	lastDecayRun  time.Time
}

// LearningStatistics tracks overall learning performance
type LearningStatistics struct {
	TotalPatterns       int       `json:"total_patterns"`
	HighConfidence      int       `json:"high_confidence"`    // ≥ 0.80
	MediumConfidence    int       `json:"medium_confidence"`  // 0.60-0.79
	LowConfidence       int       `json:"low_confidence"`     // < 0.60
	TotalApplications   int       `json:"total_applications"`
	SuccessfulApps      int       `json:"successful_apps"`
	FailedApps          int       `json:"failed_apps"`
	RejectedApps        int       `json:"rejected_apps"`
	SuccessRate         float64   `json:"success_rate"`
	HumanPatterns       int       `json:"human_patterns"`
	LastDecay           time.Time `json:"last_decay"`
	PatternsDecayed     int       `json:"patterns_decayed"`
	AvgConfidence       float64   `json:"avg_confidence"`
	MedianConfidence    float64   `json:"median_confidence"`
}

// NewLearningLoop creates a new learning loop instance
//
// Example:
//
//	db, _ := OpenDB("ananta_learning.db")
//	loop := NewLearningLoop(db)
//	loop.ProcessApplicationOutcome(patternID, outcome)
func NewLearningLoop(db *PatternDB) *LearningLoop {
	return &LearningLoop{
		db:            db,
		decayInterval: 7 * 24 * time.Hour, // Run decay weekly
		lastDecayRun:  time.Now(),
	}
}

// ProcessApplicationOutcome updates pattern confidence based on application result
//
// Reinforcement learning update rule:
//   - Success: confidence += 0.05 (reward signal, capped at 0.99)
//   - Failure: confidence -= 0.10 (penalty signal, floored at 0.10)
//   - Rejected: no change (pattern wasn't actually used)
//
// This implements a simple Q-learning style update where:
// - Confidence acts as the Q-value (expected future success)
// - Outcome is the reward/penalty
// - Learning rate is asymmetric (0.05 for success, 0.10 for failure)
//
// Asymmetric learning rates make the system cautious (faster to reduce
// confidence on failure than to increase on success).
//
// Example:
//
//	outcome := ApplicationOutcome{
//	    PatternID: 42,
//	    Outcome: OutcomeSuccess,
//	    CompilationSuccess: true,
//	    TestPass: true,
//	}
//	err := loop.ProcessApplicationOutcome(42, outcome)
func (l *LearningLoop) ProcessApplicationOutcome(
	patternID int64,
	outcome ApplicationOutcome,
) error {
	// Record the application in database
	if err := RecordApplication(l.db, outcome); err != nil {
		return fmt.Errorf("failed to record application: %w", err)
	}

	// Update confidence based on outcome type
	if err := UpdateConfidenceFromOutcome(l.db, patternID, outcome.Outcome); err != nil {
		return fmt.Errorf("failed to update confidence: %w", err)
	}

	return nil
}

// DecayOldPatterns applies temporal decay to unused patterns
//
// Temporal discounting mechanism:
// - Patterns unused for > 90 days: confidence × 0.95 (5% reduction)
// - This implements exponential decay: e^(-λt) approximated by geometric series
// - After 90 days: 0.95x original
// - After 180 days: 0.90x original (0.95²)
// - After 365 days: 0.81x original (0.95⁴)
//
// Rationale:
// - Codebases evolve; old patterns may become obsolete
// - Encourages fresh patterns to rise in rankings
// - Prevents stale patterns from blocking new learning
//
// This is inspired by:
// - Ebbinghaus forgetting curve (memory decay over time)
// - Cache eviction policies (LRU-style temporal discounting)
// - Explore-exploit tradeoff (reduce confidence in stale patterns to enable exploration)
//
// Example:
//
//	ctx := context.Background()
//	decayed, err := loop.DecayOldPatterns(ctx)
//	fmt.Printf("Decayed %d patterns\n", decayed)
func (l *LearningLoop) DecayOldPatterns(ctx context.Context) error {
	// Apply decay to patterns unused for > 90 days
	if err := ApplyTemporalDecay(l.db, 90*24*time.Hour); err != nil {
		return fmt.Errorf("failed to apply temporal decay: %w", err)
	}

	l.lastDecayRun = time.Now()
	return nil
}

// LearnFromHumanSolution adds a new pattern from human expert
//
// Transfer learning from human expertise:
// - Human-verified patterns start at confidence = 0.85 (HIGH tier)
// - Repo source = "human:manual" for attribution
// - Quality score = 0.85 (assumed high quality)
//
// Rationale:
// - Humans verify solutions work before submitting
// - Higher initial confidence than mined patterns (which start at 0.50)
// - Can still improve or decay based on subsequent application outcomes
//
// This implements knowledge distillation:
// - Expert (human) distills knowledge into pattern database
// - System learns from both automated mining AND expert input
// - Combines the best of supervised (human) and unsupervised (mining) learning
//
// Example:
//
//	metadata := HumanPatternMetadata{
//	    AuthorName: "alice@example.com",
//	    Description: "Fix for nil pointer in HTTP handler",
//	    Source: "code_review",
//	}
//	pattern, err := loop.LearnFromHumanSolution(
//	    "3:a1b2c3d4",
//	    "if x == nil { return errors.New(\"nil\") }",
//	    metadata,
//	)
func (l *LearningLoop) LearnFromHumanSolution(
	errorSignature string,
	solutionCode string,
	metadata HumanPatternMetadata,
) (*Pattern, error) {
	pattern, err := AddHumanPattern(
		l.db,
		errorSignature,
		solutionCode,
		metadata.Language,
		metadata.Category,
		metadata,
	)
	if err != nil {
		return nil, fmt.Errorf("failed to add human pattern: %w", err)
	}

	return pattern, nil
}

// GetStatistics returns overall learning performance metrics
//
// Computes:
// - Confidence distribution (HIGH/MEDIUM/LOW tiers)
// - Application success rate
// - Temporal decay status
// - Average/median confidence
//
// These metrics enable:
// - Monitoring learning progress
// - Detecting degradation (falling success rate)
// - Tuning hyperparameters (decay rate, learning rates)
//
// Example:
//
//	stats, err := loop.GetStatistics()
//	fmt.Printf("Success rate: %.2f%%\n", stats.SuccessRate * 100)
//	fmt.Printf("High confidence: %d patterns\n", stats.HighConfidence)
func (l *LearningLoop) GetStatistics() (*LearningStatistics, error) {
	stats := &LearningStatistics{
		LastDecay: l.lastDecayRun,
	}

	// Query total patterns and confidence distribution
	query := `
		SELECT
			COUNT(*) as total,
			SUM(CASE WHEN confidence >= 0.80 THEN 1 ELSE 0 END) as high,
			SUM(CASE WHEN confidence >= 0.60 AND confidence < 0.80 THEN 1 ELSE 0 END) as medium,
			SUM(CASE WHEN confidence < 0.60 THEN 1 ELSE 0 END) as low,
			AVG(confidence) as avg_conf
		FROM patterns
	`

	err := l.db.db.QueryRow(query).Scan(
		&stats.TotalPatterns,
		&stats.HighConfidence,
		&stats.MediumConfidence,
		&stats.LowConfidence,
		&stats.AvgConfidence,
	)
	if err != nil {
		return nil, fmt.Errorf("failed to query pattern stats: %w", err)
	}

	// Query application statistics
	appQuery := `
		SELECT
			COUNT(*) as total,
			SUM(CASE WHEN outcome = 'success' THEN 1 ELSE 0 END) as success,
			SUM(CASE WHEN outcome = 'failure' THEN 1 ELSE 0 END) as failure,
			SUM(CASE WHEN outcome = 'rejected' THEN 1 ELSE 0 END) as rejected
		FROM applications
	`

	err = l.db.db.QueryRow(appQuery).Scan(
		&stats.TotalApplications,
		&stats.SuccessfulApps,
		&stats.FailedApps,
		&stats.RejectedApps,
	)
	if err != nil {
		return nil, fmt.Errorf("failed to query application stats: %w", err)
	}

	// Calculate success rate (excluding rejected applications)
	actualAttempts := stats.SuccessfulApps + stats.FailedApps // Don't count rejected
	if actualAttempts > 0 {
		stats.SuccessRate = float64(stats.SuccessfulApps) / float64(actualAttempts)
	}

	// Count human-added patterns
	humanQuery := `SELECT COUNT(*) FROM patterns WHERE repo_sources LIKE '%"human:manual"%'`
	err = l.db.db.QueryRow(humanQuery).Scan(&stats.HumanPatterns)
	if err != nil {
		return nil, fmt.Errorf("failed to query human patterns: %w", err)
	}

	// Get median confidence
	medianQuery := `
		SELECT confidence
		FROM patterns
		ORDER BY confidence
		LIMIT 1
		OFFSET (SELECT COUNT(*) FROM patterns) / 2
	`
	err = l.db.db.QueryRow(medianQuery).Scan(&stats.MedianConfidence)
	if err != nil {
		// Median might not exist for empty table, ignore error
		stats.MedianConfidence = 0.0
	}

	return stats, nil
}
