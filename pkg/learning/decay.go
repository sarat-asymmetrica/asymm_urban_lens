// Package learning implements temporal decay for pattern confidence
//
// Decay: Exponential decay for unused patterns (forgetting mechanism)
// Author: Agent 1.3 (Dr. Chen Wei)
// Created: 2025-11-07
package learning

import (
	"fmt"
	"math"
	"time"
)

// CalculateDecayFactor computes decay multiplier based on time since last use
//
// Exponential decay model:
//
//	decay_factor = e^(-λt)
//
// Where:
//   - λ = decay rate constant (1/90 days, so half-life ≈ 62 days)
//   - t = time since last applied (in days)
//
// Approximated as geometric decay for computational efficiency:
//
//	decay_factor = 0.95 per 90 days
//
// Timeline:
//   - 0 days: 1.00× (no decay)
//   - 90 days: 0.95× (5% reduction)
//   - 180 days: 0.90× (10% reduction cumulative)
//   - 365 days: 0.81× (19% reduction cumulative)
//   - 730 days: 0.66× (34% reduction cumulative)
//
// Rationale:
// - Codebases evolve; best practices change
// - Old patterns may become obsolete (language updates, library changes)
// - Encourages exploration of new patterns
// - Prevents stale patterns from dominating rankings
//
// Inspired by:
// - Ebbinghaus forgetting curve (memory decay)
// - Cache eviction (LRU temporal discounting)
// - Multi-armed bandit (time-decayed rewards)
//
// Example:
//
//	lastApplied := time.Now().AddDate(0, 0, -180) // 180 days ago
//	factor := CalculateDecayFactor(lastApplied, time.Now())
//	// factor ≈ 0.90 (10% confidence reduction)
func CalculateDecayFactor(lastApplied time.Time, now time.Time) float64 {
	// Calculate days since last use
	daysSinceUse := int(now.Sub(lastApplied).Hours() / 24)

	if daysSinceUse <= 0 {
		return 1.0 // No decay for recently used patterns
	}

	// Geometric decay: 0.95 per 90-day period
	periods := float64(daysSinceUse) / 90.0
	decayFactor := math.Pow(0.95, periods)

	return decayFactor
}

// ApplyTemporalDecay reduces confidence for patterns unused for > threshold
//
// Decay algorithm:
// 1. Find all patterns with last_applied > threshold (or NULL)
// 2. Calculate decay factor based on time since last use
// 3. Update: confidence_new = confidence_old × decay_factor
// 4. Update updated_at timestamp
//
// Default threshold: 90 days
//
// Special cases:
// - Patterns never applied (last_applied IS NULL): treated as created_at
// - Human patterns: decay applies (even expert knowledge becomes stale)
// - Patterns below 0.10 confidence: no further decay (floor)
//
// Example:
//
//	db, _ := OpenDB("ananta_learning.db")
//	err := ApplyTemporalDecay(db, 90*24*time.Hour)
//	// All patterns unused for 90+ days have reduced confidence
func ApplyTemporalDecay(db *PatternDB, unusedThreshold time.Duration) error {
	// Find patterns unused for > threshold
	query := `
		SELECT id, confidence, last_applied, created_at
		FROM patterns
		WHERE (
			last_applied IS NULL
			OR julianday('now') - julianday(last_applied) > ?
		)
		AND confidence > 0.10
	`

	thresholdDays := unusedThreshold.Hours() / 24
	rows, err := db.db.Query(query, thresholdDays)
	if err != nil {
		return fmt.Errorf("failed to query patterns for decay: %w", err)
	}

	// Collect patterns to update (to avoid database locked error)
	type patternToDecay struct {
		id            int64
		confidence    float64
		lastApplied   time.Time
		newConfidence float64
	}

	var patternsToUpdate []patternToDecay
	now := time.Now()

	for rows.Next() {
		var id int64
		var confidence float64
		var lastAppliedStr, createdAtStr string

		err := rows.Scan(&id, &confidence, &lastAppliedStr, &createdAtStr)
		if err != nil {
			rows.Close()
			return fmt.Errorf("failed to scan pattern: %w", err)
		}

		// Parse timestamps
		var lastApplied time.Time
		if lastAppliedStr != "" {
			lastApplied, _ = time.Parse(time.RFC3339, lastAppliedStr)
		} else {
			// Never applied - use created_at as baseline
			lastApplied, _ = time.Parse(time.RFC3339, createdAtStr)
		}

		// Calculate decay factor
		decayFactor := CalculateDecayFactor(lastApplied, now)

		// Apply decay
		newConfidence := confidence * decayFactor

		// Floor at 0.10 (always keep exploration chance)
		if newConfidence < 0.10 {
			newConfidence = 0.10
		}

		patternsToUpdate = append(patternsToUpdate, patternToDecay{
			id:            id,
			confidence:    confidence,
			lastApplied:   lastApplied,
			newConfidence: newConfidence,
		})
	}
	rows.Close() // Close before updating

	// Now update all patterns
	for _, p := range patternsToUpdate {
		updateQuery := `UPDATE patterns SET confidence = ?, updated_at = datetime('now') WHERE id = ?`
		_, err = db.db.Exec(updateQuery, p.newConfidence, p.id)
		if err != nil {
			return fmt.Errorf("failed to update confidence for pattern %d: %w", p.id, err)
		}
	}

	return nil
}

// DecayConfidence applies decay formula to a single pattern
//
// Pure function for testing decay logic:
//
//	new_confidence = old_confidence × 0.95^(days/90)
//
// Examples:
//   - 0.80 confidence, 90 days → 0.76 (dropped from HIGH to MEDIUM)
//   - 0.60 confidence, 180 days → 0.54 (dropped from MEDIUM to LOW)
//   - 0.50 confidence, 365 days → 0.41 (significant decay)
//
// Example:
//
//	newConf := DecayConfidence(0.80, 90)
//	// newConf = 0.76 (5% reduction)
func DecayConfidence(currentConfidence float64, daysSinceUse int) float64 {
	if daysSinceUse <= 0 {
		return currentConfidence
	}

	// Geometric decay: 0.95 per 90-day period
	periods := float64(daysSinceUse) / 90.0
	decayFactor := math.Pow(0.95, periods)

	newConfidence := currentConfidence * decayFactor

	// Floor at 0.10
	if newConfidence < 0.10 {
		newConfidence = 0.10
	}

	return newConfidence
}

// GetUnusedPatterns retrieves patterns unused for > threshold
//
// Useful for:
// - Debugging decay logic
// - Identifying stale patterns
// - Pruning database (optional - we keep history)
//
// Example:
//
//	patterns, err := GetUnusedPatterns(db, 180*24*time.Hour)
//	fmt.Printf("Found %d patterns unused for 6+ months\n", len(patterns))
func GetUnusedPatterns(db *PatternDB, unusedThreshold time.Duration) ([]*Pattern, error) {
	query := `
		SELECT id, error_signature, language, category, confidence, frequency, last_applied, created_at
		FROM patterns
		WHERE (
			last_applied IS NULL
			OR julianday('now') - julianday(last_applied) > ?
		)
		ORDER BY last_applied ASC NULLS FIRST
	`

	thresholdDays := unusedThreshold.Hours() / 24
	rows, err := db.db.Query(query, thresholdDays)
	if err != nil {
		return nil, fmt.Errorf("failed to query unused patterns: %w", err)
	}
	defer rows.Close()

	var patterns []*Pattern
	for rows.Next() {
		var p Pattern
		var lastAppliedStr, createdAtStr string

		err := rows.Scan(
			&p.ID,
			&p.ErrorSig,
			&p.Language,
			&p.Category,
			&p.Confidence,
			&p.Frequency,
			&lastAppliedStr,
			&createdAtStr,
		)
		if err != nil {
			return nil, fmt.Errorf("failed to scan pattern: %w", err)
		}

		// Parse timestamps
		if lastAppliedStr != "" {
			p.LastApplied, _ = time.Parse(time.RFC3339, lastAppliedStr)
		}
		p.CreatedAt, _ = time.Parse(time.RFC3339, createdAtStr)

		patterns = append(patterns, &p)
	}

	return patterns, nil
}
