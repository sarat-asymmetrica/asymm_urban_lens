package learning

import (
	"math"
	"time"
)

// ScoreRepo calculates a composite quality score for a repository using multiple dimensions.
// Formula: score = (stars_score × 0.4) + (freshness_score × 0.3) + (ci_score × 0.2) + (docs_score × 0.1)
//
// Scoring dimensions:
// - stars_score: Logarithmic scaling (log10(stars) / log10(100000)) - 100K stars = 1.0
// - freshness_score: Exponential decay from last update (1.0 if < 3 months, decays exponentially)
// - ci_score: Binary indicator of CI/CD presence (1.0 if present, 0.0 otherwise)
// - docs_score: Documentation quality (1.0 if README + docs/, 0.5 if only README, 0.0 if neither)
//
// Returns a score between 0.0 and 1.0, where higher is better.
func ScoreRepo(stars int, lastUpdate time.Time, hasCI bool, hasDocs bool, hasDocsDir bool) float64 {
	starsScore := CalculateStarsScore(stars)
	freshnessScore := CalculateFreshnessScore(lastUpdate)
	ciScore := CalculateCIScore(hasCI)
	docsScore := CalculateDocsScore(hasDocs, hasDocsDir)

	// Weighted combination (emphasizes stars and freshness)
	score := (starsScore * 0.4) + (freshnessScore * 0.3) + (ciScore * 0.2) + (docsScore * 0.1)

	return score
}

// CalculateStarsScore normalizes star count to a 0-1 scale using logarithmic scaling.
// This prevents mega-popular repos (100K+ stars) from dominating while still rewarding popularity.
//
// Formula: log10(stars) / log10(100000)
// Examples:
// - 1 star = 0.0
// - 1000 stars = 0.6
// - 10000 stars = 0.8
// - 100000 stars = 1.0
func CalculateStarsScore(stars int) float64 {
	if stars <= 0 {
		return 0.0
	}

	// Logarithmic scaling with 100K stars as the reference point (score = 1.0)
	maxStarsLog := math.Log10(100000.0)
	starsLog := math.Log10(float64(stars))

	score := starsLog / maxStarsLog

	// Cap at 1.0 (repos with >100K stars still get max score)
	if score > 1.0 {
		return 1.0
	}

	return score
}

// CalculateFreshnessScore measures how recently a repository was updated.
// Recent updates indicate active maintenance and community engagement.
//
// Scoring:
// - Updated within last 3 months: 1.0
// - Updated 3-6 months ago: exponential decay starting
// - Updated >2 years ago: approaches 0.0
//
// Formula: e^(-λ × days_since_update) where λ = decay_rate
func CalculateFreshnessScore(lastUpdate time.Time) float64 {
	now := time.Now()
	daysSince := now.Sub(lastUpdate).Hours() / 24.0

	// If updated within last 91 days (just over 3 months), full score
	// Using 91 to handle month length variations and floating point precision
	if daysSince <= 91.0 {
		return 1.0
	}

	// Exponential decay after 91 days
	// Decay rate chosen so that 1 year old = ~0.4, 2 years old = ~0.15
	decayRate := 0.003 // Tuned for gradual decay
	score := math.Exp(-decayRate * daysSince)

	return score
}

// CalculateCIScore checks if the repository has CI/CD infrastructure.
// CI/CD indicates professional development practices and automated testing.
//
// Binary score:
// - Has CI: 1.0
// - No CI: 0.0
func CalculateCIScore(hasCI bool) float64 {
	if hasCI {
		return 1.0
	}
	return 0.0
}

// CalculateDocsScore evaluates documentation quality based on presence of README and docs directory.
// Good documentation indicates maturity and ease of learning.
//
// Scoring:
// - README + docs/ directory: 1.0 (comprehensive documentation)
// - README only: 0.5 (minimal documentation)
// - Neither: 0.0 (poor documentation)
func CalculateDocsScore(hasReadme bool, hasDocsDir bool) float64 {
	if hasReadme && hasDocsDir {
		return 1.0 // Comprehensive documentation
	}
	if hasReadme {
		return 0.5 // Minimal documentation
	}
	return 0.0 // Poor documentation
}
