// Package healing implements self-healing error matching and fix generation
//
// Match Tiers: Tier classification and statistics for pattern matching
// Author: Agent 2.2 (Dr. Elena Volkov - Information Retrieval)
// Created: 2025-11-07
package healing

import "time"

// MatchTier classifies match quality for decision making
type MatchTier string

const (
	HIGH   MatchTier = "HIGH"   // ≥0.80 - Direct apply (trust the pattern)
	MEDIUM MatchTier = "MEDIUM" // 0.60-0.79 - Swarm verification needed
	LOW    MatchTier = "LOW"    // <0.60 - Flag for review
)

// MatchStatistics provides aggregate statistics for a matching session
type MatchStatistics struct {
	TotalErrors       int       `json:"total_errors"`        // Total errors processed
	HighMatches       int       `json:"high_matches"`        // HIGH tier matches (≥0.80)
	MediumMatches     int       `json:"medium_matches"`      // MEDIUM tier matches (0.60-0.79)
	LowMatches        int       `json:"low_matches"`         // LOW tier matches (<0.60)
	NoMatches         int       `json:"no_matches"`          // Errors with no match found
	AverageScore      float64   `json:"average_score"`       // Average combined score
	AverageConfidence float64   `json:"average_confidence"`  // Average confidence score
	AverageSimilarity float64   `json:"average_similarity"`  // Average semantic similarity
	ProcessedAt       time.Time `json:"processed_at"`        // When statistics were computed
}

// GetMatchTier determines tier from PatternMatch
func GetMatchTier(match PatternMatch) MatchTier {
	return classifyTier(match.CombinedScore)
}

// classifyTier classifies match score into HIGH/MEDIUM/LOW tier
func classifyTier(score float64) MatchTier {
	if score >= 0.80 {
		return HIGH
	} else if score >= 0.60 {
		return MEDIUM
	}
	return LOW
}
