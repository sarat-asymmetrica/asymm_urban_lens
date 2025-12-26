// Package learning implements Ananta's self-healing pattern database and error classification
//
// Confidence Tiers: Classification and scoring for pattern confidence
// Author: Agent 1.2 (Dr. Sofia Hernandez - Statistician)
// Created: 2025-11-07
package learning

import (
	"math"
	"time"
)

// ConfidenceTier classifies patterns by confidence level
type ConfidenceTier string

const (
	// HIGH confidence: ≥ 0.80 (direct apply, high trust)
	HIGH ConfidenceTier = "HIGH"

	// MEDIUM confidence: 0.60-0.79 (swarm verification recommended)
	MEDIUM ConfidenceTier = "MEDIUM"

	// LOW confidence: < 0.60 (flag for review, low trust)
	LOW ConfidenceTier = "LOW"
)

// ClassifyConfidence maps confidence score to tier
//
// Thresholds:
//   - HIGH: confidence ≥ 0.80
//   - MEDIUM: 0.60 ≤ confidence < 0.80
//   - LOW: confidence < 0.60
func ClassifyConfidence(score float64) ConfidenceTier {
	if score >= 0.80 {
		return HIGH
	}
	if score >= 0.60 {
		return MEDIUM
	}
	return LOW
}

// CalculateConfidence computes confidence score for a pattern
//
// Formula:
//
//	confidence = (repo_frequency × 0.6) + (pattern_quality × 0.3) + (recency × 0.1)
//
// WHERE:
//   - repo_frequency: MIN(1.0, repos_with_pattern / 10)  [0, 1]
//   - pattern_quality: success_count / (success + failure) if applied, else 0.5  [0, 1]
//   - recency: exp(-days_since_discovery / 365)  [0, 1]
//
// Returns: confidence ∈ [0.0, 1.0]
func CalculateConfidence(pattern *Pattern, totalRepos int) float64 {
	repoFreq := CalculateRepoFrequency(pattern, totalRepos)
	quality := CalculatePatternQuality(pattern)
	recency := CalculateRecency(pattern)

	// Weighted sum: 60% frequency, 30% quality, 10% recency
	confidence := (repoFreq * 0.6) + (quality * 0.3) + (recency * 0.1)

	// Clamp to [0, 1]
	if confidence < 0.0 {
		confidence = 0.0
	}
	if confidence > 1.0 {
		confidence = 1.0
	}

	return confidence
}

// CalculateRepoFrequency computes how frequently pattern appears across repos
//
// Formula:
//
//	repo_frequency = MIN(1.0, repos_with_pattern / 10)
//
// Rationale:
//   - If pattern appears in 10+ repos → frequency = 1.0 (saturates)
//   - If pattern appears in 5 repos → frequency = 0.5
//   - If pattern appears in 1 repo → frequency = 0.1
//
// This caps frequency at 10 repos to prevent over-weighting extremely common patterns.
func CalculateRepoFrequency(pattern *Pattern, totalRepos int) float64 {
	repoCount := len(pattern.RepoSources)

	// Edge case: no repo sources
	if repoCount == 0 {
		return 0.0
	}

	// Frequency calculation with saturation at 10 repos
	frequency := float64(repoCount) / 10.0

	// Clamp to [0, 1]
	if frequency > 1.0 {
		frequency = 1.0
	}

	return frequency
}

// CalculatePatternQuality computes success rate of pattern applications
//
// Formula:
//
//	IF pattern has been applied:
//	    quality = success_count / (success_count + failure_count)
//	ELSE:
//	    quality = 0.5  (neutral, no data)
//
// Rationale:
//   - Proven patterns: Quality reflects actual performance
//   - Unapplied patterns: Neutral score (no evidence yet)
//   - All failures: quality = 0.0
//   - All successes: quality = 1.0
func CalculatePatternQuality(pattern *Pattern) float64 {
	totalApplications := pattern.SuccessCount + pattern.FailureCount

	// No applications yet → neutral quality
	if totalApplications == 0 {
		return 0.5
	}

	// Calculate success rate
	quality := float64(pattern.SuccessCount) / float64(totalApplications)

	return quality
}

// CalculateRecency computes temporal decay for pattern freshness
//
// Formula:
//
//	recency = exp(-days_since_discovery / 365)
//
// Decay characteristics:
//   - Fresh patterns (0 days): recency = 1.0
//   - 6 months old: recency ≈ 0.61
//   - 1 year old: recency ≈ 0.37
//   - 2 years old: recency ≈ 0.14
//   - 3 years old: recency ≈ 0.05
//
// Rationale:
//   - Programming best practices evolve
//   - Old patterns may be deprecated
//   - Exponential decay models real-world pattern obsolescence
func CalculateRecency(pattern *Pattern) float64 {
	// Calculate days since pattern was created
	now := time.Now()
	daysSinceCreation := now.Sub(pattern.CreatedAt).Hours() / 24.0

	// Edge case: future date (system clock issues)
	if daysSinceCreation < 0 {
		return 1.0 // Treat as fresh
	}

	// Exponential decay: half-life of 1 year
	recency := math.Exp(-daysSinceCreation / 365.0)

	return recency
}

// ConfidenceDistribution summarizes confidence tier counts
type ConfidenceDistribution struct {
	High   int     `json:"high"`   // Count of HIGH tier patterns
	Medium int     `json:"medium"` // Count of MEDIUM tier patterns
	Low    int     `json:"low"`    // Count of LOW tier patterns
	Total  int     `json:"total"`  // Total patterns
	AvgConfidence float64 `json:"avg_confidence"` // Average confidence (harmonic mean)
}

// CalculateDistribution computes confidence distribution for patterns
//
// Returns:
//   - Counts for each tier (HIGH, MEDIUM, LOW)
//   - Average confidence using harmonic mean (penalizes low outliers)
func CalculateDistribution(patterns []*Pattern) *ConfidenceDistribution {
	dist := &ConfidenceDistribution{}

	if len(patterns) == 0 {
		return dist
	}

	var sumReciprocals float64

	for _, p := range patterns {
		dist.Total++

		tier := ClassifyConfidence(p.Confidence)
		switch tier {
		case HIGH:
			dist.High++
		case MEDIUM:
			dist.Medium++
		case LOW:
			dist.Low++
		}

		// Harmonic mean accumulation
		if p.Confidence > 0 {
			sumReciprocals += 1.0 / p.Confidence
		}
	}

	// Calculate harmonic mean: n / Σ(1/x_i)
	if sumReciprocals > 0 {
		dist.AvgConfidence = float64(dist.Total) / sumReciprocals
	}

	return dist
}
