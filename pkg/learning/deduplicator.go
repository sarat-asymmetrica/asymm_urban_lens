// Package learning implements Ananta's self-healing pattern database and error classification
//
// Deduplicator: Removes duplicate patterns using hash and structural similarity
// Author: Agent 6.2 (Dr. Yuki Tanaka - Data Quality & ML Specialist)
// Created: 2025-11-07
package learning

import (
	"fmt"
	"sort"
)

// PatternDeduplicator finds and merges duplicate patterns
type PatternDeduplicator struct {
	similarityThreshold float64 // Default: 0.85
}

// NewPatternDeduplicator creates a deduplicator with default threshold
func NewPatternDeduplicator() *PatternDeduplicator {
	return &PatternDeduplicator{
		similarityThreshold: 0.85,
	}
}

// DeduplicationStats tracks deduplication results
type DeduplicationStats struct {
	Original      int     // Original pattern count
	Duplicates    int     // Exact duplicates found
	Merged        int     // Similar patterns merged
	Final         int     // Final unique pattern count
	DuplicateRate float64 // Percentage of duplicates (0.0-1.0)
}

// DeduplicatePatterns removes duplicates from pattern list
//
// Algorithm:
//  1. Group by error signature (exact matches must have same signature)
//  2. Within each group, find exact duplicates by hash
//  3. For remaining patterns, find similar ones by structural comparison
//  4. Merge duplicates (keep highest confidence, sum frequencies)
//  5. Return deduplicated list with statistics
//
// Performance: O(n log n) for grouping + O(k²) for similarity within groups
// where k = avg group size (typically k << n)
func (pd *PatternDeduplicator) DeduplicatePatterns(patterns []*Pattern) ([]*Pattern, *DeduplicationStats) {
	stats := &DeduplicationStats{
		Original: len(patterns),
	}

	if len(patterns) == 0 {
		stats.Final = 0
		return patterns, stats
	}

	// PHASE 1: Group by error signature
	// Patterns with different signatures can't be duplicates
	groups := groupBySignature(patterns)

	// PHASE 2: Deduplicate within each group
	var deduplicated []*Pattern
	for _, group := range groups {
		if len(group) == 1 {
			deduplicated = append(deduplicated, group[0])
			continue
		}

		// Deduplicate this group
		uniquePatterns, groupStats := pd.deduplicateGroup(group)
		deduplicated = append(deduplicated, uniquePatterns...)

		stats.Duplicates += groupStats.Duplicates
		stats.Merged += groupStats.Merged
	}

	stats.Final = len(deduplicated)
	if stats.Original > 0 {
		stats.DuplicateRate = float64(stats.Original-stats.Final) / float64(stats.Original)
	}

	return deduplicated, stats
}

// deduplicateGroup deduplicates patterns within a single signature group
func (pd *PatternDeduplicator) deduplicateGroup(group []*Pattern) ([]*Pattern, *DeduplicationStats) {
	stats := &DeduplicationStats{
		Original: len(group),
	}

	// PHASE 1: Group by solution hash (exact duplicates)
	hashGroups := GroupByHash(group)

	// PHASE 2: For each hash group, merge exact duplicates
	var candidates []*Pattern
	for _, hashGroup := range hashGroups {
		if len(hashGroup) == 1 {
			candidates = append(candidates, hashGroup[0])
		} else {
			// Multiple patterns with same hash = exact duplicates
			merged := pd.MergePatterns(hashGroup)
			candidates = append(candidates, merged)
			stats.Duplicates += len(hashGroup) - 1
		}
	}

	// PHASE 3: Find similar patterns among remaining candidates
	// Use greedy clustering: compare each pattern to already-accepted patterns
	var unique []*Pattern
	for _, candidate := range candidates {
		// Check if similar to any already-accepted pattern
		var similarTo *Pattern
		var bestSim float64

		for _, existing := range unique {
			isSim, sim := AreSimilar(candidate, existing)
			if isSim && sim > bestSim {
				similarTo = existing
				bestSim = sim
			}
		}

		if similarTo != nil {
			// Merge with similar pattern
			*similarTo = *pd.MergePatterns([]*Pattern{similarTo, candidate})
			stats.Merged++
		} else {
			// New unique pattern
			unique = append(unique, candidate)
		}
	}

	stats.Final = len(unique)

	return unique, stats
}

// groupBySignature groups patterns by error signature
func groupBySignature(patterns []*Pattern) map[string][]*Pattern {
	groups := make(map[string][]*Pattern)
	for _, p := range patterns {
		groups[p.ErrorSig] = append(groups[p.ErrorSig], p)
	}
	return groups
}

// AreDuplicates checks if two patterns are duplicates
//
// Returns:
//   - bool: true if duplicate (exact hash match OR structural similarity ≥ 0.85)
//   - float64: similarity score [0.0, 1.0]
func (pd *PatternDeduplicator) AreDuplicates(p1, p2 *Pattern) (bool, float64) {
	// Must have same error signature to be duplicates
	if p1.ErrorSig != p2.ErrorSig {
		return false, 0.0
	}

	return AreSimilar(p1, p2)
}

// MergePatterns combines duplicate patterns into a single pattern
//
// Merge strategy:
//  1. Solution: Keep from pattern with highest confidence
//  2. Confidence: Weighted average by frequency
//  3. Frequency: Sum all frequencies
//  4. Success/Failure counts: Sum all counts
//  5. RepoSources: Union of all repo IDs
//  6. Timestamps: Keep earliest created_at, latest updated_at
//
// This preserves the best solution while accumulating evidence.
func (pd *PatternDeduplicator) MergePatterns(patterns []*Pattern) *Pattern {
	if len(patterns) == 0 {
		return nil
	}
	if len(patterns) == 1 {
		return patterns[0]
	}

	// Sort by confidence DESC to pick best solution
	sort.Slice(patterns, func(i, j int) bool {
		return patterns[i].Confidence > patterns[j].Confidence
	})

	// Start with highest-confidence pattern
	merged := &Pattern{
		ErrorSig:     patterns[0].ErrorSig,
		ErrorType:    patterns[0].ErrorType,
		Language:     patterns[0].Language,
		Category:     patterns[0].Category,
		SolutionCode: patterns[0].SolutionCode, // Best solution
		SolutionHash: patterns[0].SolutionHash,
	}

	// Accumulate statistics
	var totalFreq int
	var weightedConfidence float64
	var repoSourcesMap = make(map[int64]bool)
	var earliestCreated = patterns[0].CreatedAt
	var latestUpdated = patterns[0].UpdatedAt

	for _, p := range patterns {
		// Sum frequencies
		totalFreq += p.Frequency
		merged.SuccessCount += p.SuccessCount
		merged.FailureCount += p.FailureCount

		// Weighted average of confidence (by frequency)
		weightedConfidence += p.Confidence * float64(p.Frequency)

		// Union of repo sources
		for _, repoID := range p.RepoSources {
			repoSourcesMap[repoID] = true
		}

		// Track earliest/latest timestamps
		if !p.CreatedAt.IsZero() && (earliestCreated.IsZero() || p.CreatedAt.Before(earliestCreated)) {
			earliestCreated = p.CreatedAt
		}
		if !p.UpdatedAt.IsZero() && p.UpdatedAt.After(latestUpdated) {
			latestUpdated = p.UpdatedAt
		}
		if !p.LastApplied.IsZero() && p.LastApplied.After(merged.LastApplied) {
			merged.LastApplied = p.LastApplied
		}
	}

	merged.Frequency = totalFreq
	if totalFreq > 0 {
		merged.Confidence = weightedConfidence / float64(totalFreq)
	}

	// Convert repo sources map to slice
	merged.RepoSources = make([]int64, 0, len(repoSourcesMap))
	for repoID := range repoSourcesMap {
		merged.RepoSources = append(merged.RepoSources, repoID)
	}

	merged.CreatedAt = earliestCreated
	merged.UpdatedAt = latestUpdated

	return merged
}

// String formats deduplication stats for display
func (s *DeduplicationStats) String() string {
	return fmt.Sprintf("Original: %d, Duplicates: %d, Merged: %d, Final: %d (%.1f%% reduction)",
		s.Original, s.Duplicates, s.Merged, s.Final, s.DuplicateRate*100)
}
