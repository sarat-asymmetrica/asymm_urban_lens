// Package learning implements Ananta's self-healing pattern database and error classification
//
// Merger: Merges new patterns with existing pattern database
// Author: Agent 6.2 (Dr. Yuki Tanaka - Data Quality & ML Specialist)
// Created: 2025-11-07
package learning

import (
	"fmt"
)

// PatternMerger merges new patterns into existing database
type PatternMerger struct {
	db                  *PatternDB
	similarityThreshold float64 // Threshold for considering patterns similar (default 0.85)
}

// NewPatternMerger creates a merger with database connection
func NewPatternMerger(db *PatternDB) *PatternMerger {
	return &PatternMerger{
		db:                  db,
		similarityThreshold: 0.85,
	}
}

// MergeStats tracks merge operation results
type MergeStats struct {
	NewPatterns     int // Patterns added as new
	UpdatedPatterns int // Existing patterns updated
	SkippedPatterns int // Patterns skipped (low quality, duplicates)
	TotalBefore     int // Pattern count before merge
	TotalAfter      int // Pattern count after merge
}

// MergePatterns adds new patterns to database
//
// Algorithm:
//  1. For each new pattern:
//     a. Search DB for patterns with same error signature
//     b. If similar pattern exists (similarity ≥ 0.85):
//        - Merge new pattern into existing (update confidence, frequency)
//        - UpdatedPatterns++
//     c. If no similar pattern:
//        - Add as new pattern
//        - NewPatterns++
//  2. Return statistics
//
// This prevents duplicate patterns while accumulating evidence.
func (pm *PatternMerger) MergePatterns(newPatterns []*Pattern) (*MergeStats, error) {
	stats := &MergeStats{}

	// Get count before merge (this is approximate - would need full DB count)
	// For now, we'll track only the changes
	stats.TotalBefore = 0 // Would query: SELECT COUNT(*) FROM patterns

	for _, newPattern := range newPatterns {
		// Skip patterns with very low confidence
		if newPattern.Confidence < 0.30 {
			stats.SkippedPatterns++
			continue
		}

		// Find similar patterns in DB
		existingPattern, similarity, err := pm.FindSimilarInDB(newPattern)
		if err != nil {
			return nil, fmt.Errorf("failed to find similar pattern: %w", err)
		}

		if existingPattern != nil && similarity >= pm.similarityThreshold {
			// MERGE: Update existing pattern
			merged := pm.UpdateExistingPattern(existingPattern, newPattern)

			// Update in database
			if err := pm.db.AddPattern(merged); err != nil {
				return nil, fmt.Errorf("failed to update pattern: %w", err)
			}

			stats.UpdatedPatterns++
		} else {
			// NEW: Add as new pattern
			if err := pm.db.AddPattern(newPattern); err != nil {
				return nil, fmt.Errorf("failed to add new pattern: %w", err)
			}

			stats.NewPatterns++
		}
	}

	stats.TotalAfter = stats.TotalBefore + stats.NewPatterns

	return stats, nil
}

// FindSimilarInDB searches for similar patterns in database
//
// Returns:
//   - *Pattern: Most similar pattern found (or nil)
//   - float64: Similarity score [0.0, 1.0]
//   - error: Database error if any
//
// Algorithm:
//  1. Query patterns with same error signature and language
//  2. For each candidate, compute structural similarity
//  3. Return pattern with highest similarity (if any above threshold)
func (pm *PatternMerger) FindSimilarInDB(pattern *Pattern) (*Pattern, float64, error) {
	// Query candidates: same signature, same language, confidence ≥ 0.30
	candidates, err := pm.db.FindPatterns(pattern.ErrorSig, pattern.Language, 0.30)
	if err != nil {
		return nil, 0.0, fmt.Errorf("failed to query patterns: %w", err)
	}

	if len(candidates) == 0 {
		return nil, 0.0, nil // No similar patterns
	}

	// Find most similar candidate
	var bestMatch *Pattern
	var bestSimilarity float64

	for _, candidate := range candidates {
		_, similarity := AreSimilar(pattern, candidate)

		if similarity > bestSimilarity {
			bestMatch = candidate
			bestSimilarity = similarity
		}
	}

	return bestMatch, bestSimilarity, nil
}

// UpdateExistingPattern merges new pattern data into existing pattern
//
// Merge strategy:
//  1. Solution: Keep solution from higher-confidence pattern
//  2. Confidence: Weighted average (by frequency)
//  3. Frequency: Sum frequencies
//  4. Success/Failure: Sum counts
//  5. RepoSources: Union of repo IDs
//  6. LastApplied: Keep most recent
//
// This accumulates evidence while preserving the best solution.
func (pm *PatternMerger) UpdateExistingPattern(existing, new *Pattern) *Pattern {
	// Start with existing pattern
	updated := &Pattern{
		ID:           existing.ID, // Keep existing ID
		ErrorSig:     existing.ErrorSig,
		ErrorType:    existing.ErrorType,
		Language:     existing.Language,
		Category:     existing.Category,
		SolutionHash: existing.SolutionHash,
		CreatedAt:    existing.CreatedAt, // Keep original creation time
	}

	// Choose better solution (higher confidence)
	if new.Confidence > existing.Confidence {
		updated.SolutionCode = new.SolutionCode
		updated.SolutionHash = new.SolutionHash
	} else {
		updated.SolutionCode = existing.SolutionCode
	}

	// Weighted average of confidence
	totalFreq := existing.Frequency + new.Frequency
	if totalFreq > 0 {
		updated.Confidence = (existing.Confidence*float64(existing.Frequency) +
			new.Confidence*float64(new.Frequency)) / float64(totalFreq)
	} else {
		updated.Confidence = (existing.Confidence + new.Confidence) / 2.0
	}

	// Sum frequencies and counts
	updated.Frequency = existing.Frequency + new.Frequency
	updated.SuccessCount = existing.SuccessCount + new.SuccessCount
	updated.FailureCount = existing.FailureCount + new.FailureCount

	// Union of repo sources
	repoMap := make(map[int64]bool)
	for _, repoID := range existing.RepoSources {
		repoMap[repoID] = true
	}
	for _, repoID := range new.RepoSources {
		repoMap[repoID] = true
	}

	updated.RepoSources = make([]int64, 0, len(repoMap))
	for repoID := range repoMap {
		updated.RepoSources = append(updated.RepoSources, repoID)
	}

	// Keep most recent LastApplied
	if new.LastApplied.After(existing.LastApplied) {
		updated.LastApplied = new.LastApplied
	} else {
		updated.LastApplied = existing.LastApplied
	}

	// Update timestamp
	updated.UpdatedAt = new.UpdatedAt
	if updated.UpdatedAt.IsZero() {
		updated.UpdatedAt = existing.UpdatedAt
	}

	return updated
}

// String formats merge stats for display
func (s *MergeStats) String() string {
	return fmt.Sprintf("New: %d, Updated: %d, Skipped: %d, Total: %d → %d",
		s.NewPatterns, s.UpdatedPatterns, s.SkippedPatterns,
		s.TotalBefore, s.TotalAfter)
}
