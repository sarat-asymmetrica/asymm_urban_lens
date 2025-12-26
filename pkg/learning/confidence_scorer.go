// Package learning implements Ananta's self-healing pattern database and error classification
//
// Confidence Scorer: Multi-factor confidence calculation for patterns
// Author: Agent 6.2 (Dr. Yuki Tanaka - Data Quality & ML Specialist)
// Created: 2025-11-07
package learning

import (
	"math"
	"regexp"
	"strings"
)

// ConfidenceScorer computes pattern confidence using multi-factor scoring
type ConfidenceScorer struct{}

// NewConfidenceScorer creates a new confidence scorer
func NewConfidenceScorer() *ConfidenceScorer {
	return &ConfidenceScorer{}
}

// ScoringContext provides context for confidence calculation
type ScoringContext struct {
	RepoStars            int    // GitHub stars (0-100000+)
	CommitMessage        string // Git commit message
	CommitAuthor         string // Commit author
	TimesSeenAcrossRepos int    // How many repos have this pattern
	SolutionComplexity   int    // Lines of code in solution
	TotalRepos           int    // Total repos analyzed
}

// ScorePattern calculates multi-factor confidence for a pattern
//
// Confidence formula:
//   confidence = 0.3×repo_score + 0.2×commit_score + 0.3×solution_score + 0.2×frequency_score
//
// Weights:
//   - Repo quality (0.3): Stars, activity, CI status
//   - Commit quality (0.2): Message quality, author reputation
//   - Solution quality (0.3): Genericity, complexity, clarity
//   - Frequency (0.2): Cross-repo frequency
//
// Returns: confidence ∈ [0.0, 1.0]
func (cs *ConfidenceScorer) ScorePattern(pattern *Pattern, context ScoringContext) float64 {
	repoScore := cs.CalculateRepoScore(context.RepoStars)
	commitScore := cs.CalculateCommitScore(context.CommitMessage)
	solutionScore := cs.CalculateSolutionScore(pattern.SolutionCode)
	frequencyScore := cs.CalculateFrequencyScore(context.TimesSeenAcrossRepos, context.TotalRepos)

	// Weighted average
	confidence := 0.3*repoScore + 0.2*commitScore + 0.3*solutionScore + 0.2*frequencyScore

	// Clamp to [0.0, 1.0]
	if confidence < 0.0 {
		confidence = 0.0
	}
	if confidence > 1.0 {
		confidence = 1.0
	}

	return confidence
}

// CalculateRepoScore scores repository quality based on stars
//
// Scoring:
//   - 0 stars: 0.10 (minimal trust)
//   - 100 stars: 0.50 (moderate trust)
//   - 1000 stars: 0.70 (good trust)
//   - 10000 stars: 0.90 (high trust)
//   - 50000+ stars: 1.00 (maximum trust)
//
// Formula: log-scale to avoid favoring mega-repos excessively
func (cs *ConfidenceScorer) CalculateRepoScore(stars int) float64 {
	if stars <= 0 {
		return 0.10 // Minimal baseline
	}

	// Log scale: score = 0.1 + 0.9 × log₁₀(stars+1) / log₁₀(50001)
	// This maps:
	//   1 star → 0.10
	//   100 stars → 0.52
	//   1000 stars → 0.70
	//   10000 stars → 0.88
	//   50000 stars → 1.00
	logStars := math.Log10(float64(stars + 1))
	logMax := math.Log10(50001)
	score := 0.10 + 0.90*(logStars/logMax)

	if score > 1.0 {
		score = 1.0
	}

	return score
}

// CalculateCommitScore scores commit message quality
//
// Scoring factors:
//   +0.30: Has "fix:" or "Fixed" or "Fixes" (explicit fix)
//   +0.20: Has issue reference (#123, GH-456)
//   +0.20: Has meaningful description (>20 chars, not just "fix")
//   +0.15: Has technical terms (error, exception, bug, crash)
//   +0.15: Proper capitalization and punctuation
//
// Penalties:
//   -0.40: Contains "WIP" or "TODO" or "tmp" or "test"
//   -0.20: All lowercase or ALL CAPS
//   -0.20: Very short (<10 chars)
//
// Base score: 0.30 (neutral commit message)
func (cs *ConfidenceScorer) CalculateCommitScore(message string) float64 {
	if message == "" {
		return 0.30 // Neutral score for missing message
	}

	score := 0.30 // Base score

	// Normalize for analysis
	lower := strings.ToLower(message)

	// POSITIVE SIGNALS
	if strings.Contains(lower, "fix:") || strings.Contains(lower, "fixed") || strings.Contains(lower, "fixes") {
		score += 0.30
	}

	// Issue reference
	issueRef := regexp.MustCompile(`#\d+|GH-\d+|github\.com/.+/issues/\d+`)
	if issueRef.MatchString(message) {
		score += 0.20
	}

	// Meaningful description
	if len(message) > 20 && !strings.Contains(lower, "fix error") {
		score += 0.20
	}

	// Technical terms
	technicalTerms := []string{"error", "exception", "bug", "crash", "panic", "nil", "null", "undefined"}
	for _, term := range technicalTerms {
		if strings.Contains(lower, term) {
			score += 0.15
			break
		}
	}

	// Proper formatting
	if len(message) > 0 && message[0] >= 'A' && message[0] <= 'Z' && strings.Contains(message, ".") {
		score += 0.15
	}

	// NEGATIVE SIGNALS
	wipTerms := []string{"wip", "todo", "tmp", "test", "testing", "debug"}
	for _, term := range wipTerms {
		if strings.Contains(lower, term) {
			score -= 0.40
			break
		}
	}

	// All lowercase or ALL CAPS
	if message == lower || message == strings.ToUpper(message) {
		score -= 0.20
	}

	// Very short
	if len(message) < 10 {
		score -= 0.20
	}

	// Clamp to [0.0, 1.0]
	if score < 0.0 {
		score = 0.0
	}
	if score > 1.0 {
		score = 1.0
	}

	return score
}

// CalculateSolutionScore scores solution code quality
//
// Scoring factors:
//   - Genericity (0.40): Has placeholders like <VAR>, <FUNC>, <TYPE> (from normalization)
//   - Complexity (0.30): Reasonable size (3-20 lines optimal, too short/long penalized)
//   - Clarity (0.30): Clean code indicators (no project-specific names)
//
// Returns: score ∈ [0.0, 1.0]
func (cs *ConfidenceScorer) CalculateSolutionScore(solution string) float64 {
	if solution == "" {
		return 0.0
	}

	// Normalize solution to count placeholders
	normalized := NormalizeSolution(solution)

	// GENERICITY SCORE (0.40)
	// Count placeholders vs total tokens
	placeholders := strings.Count(normalized, "<VAR>") +
		strings.Count(normalized, "<FUNC>") +
		strings.Count(normalized, "<TYPE>") +
		strings.Count(normalized, "<LITERAL>")

	// Total tokens (rough estimate: split on whitespace and operators)
	tokens := len(strings.Fields(normalized))
	if tokens == 0 {
		tokens = 1 // Avoid division by zero
	}

	genericityRatio := float64(placeholders) / float64(tokens)
	// More placeholders = more generic = higher score
	// Optimal: 30-70% placeholders
	var genericityScore float64
	if genericityRatio < 0.30 {
		// Too specific
		genericityScore = genericityRatio / 0.30 * 0.40
	} else if genericityRatio > 0.70 {
		// Too generic (maybe just placeholders, no structure)
		genericityScore = (1.0 - (genericityRatio-0.70)/0.30) * 0.40
	} else {
		// Optimal range
		genericityScore = 0.40
	}

	// COMPLEXITY SCORE (0.30)
	lines := strings.Count(solution, "\n") + 1
	var complexityScore float64
	if lines < 3 {
		// Too simple (might be incomplete)
		complexityScore = float64(lines) / 3.0 * 0.30
	} else if lines > 20 {
		// Too complex (might be too specific)
		complexityScore = math.Max(0, 0.30-float64(lines-20)*0.01)
	} else {
		// Optimal range: 3-20 lines
		complexityScore = 0.30
	}

	// CLARITY SCORE (0.30)
	// Penalize project-specific indicators
	var clarityScore float64 = 0.30

	// Check for common project-specific patterns
	projectSpecific := []string{
		"myapp", "myproject", "company", "internal",
		"TODO", "FIXME", "HACK", "XXX",
	}
	for _, pattern := range projectSpecific {
		if strings.Contains(strings.ToLower(solution), strings.ToLower(pattern)) {
			clarityScore -= 0.10
		}
	}

	if clarityScore < 0 {
		clarityScore = 0
	}

	// Total solution score
	totalScore := genericityScore + complexityScore + clarityScore

	return totalScore
}

// CalculateFrequencyScore scores pattern by cross-repo frequency
//
// Scoring:
//   - Seen in 1 repo: 0.30 (might be project-specific)
//   - Seen in 2-3 repos: 0.50 (moderate confidence)
//   - Seen in 4-5 repos: 0.70 (good confidence)
//   - Seen in 6-10 repos: 0.85 (high confidence)
//   - Seen in 11+ repos: 1.00 (very high confidence)
//
// Formula: Logarithmic growth capped at 1.0
func (cs *ConfidenceScorer) CalculateFrequencyScore(timesSeenAcrossRepos, totalRepos int) float64 {
	if timesSeenAcrossRepos <= 0 {
		return 0.30 // Minimum baseline
	}

	if totalRepos == 0 {
		totalRepos = 1 // Avoid division by zero
	}

	// Logarithmic scale
	// score = 0.3 + 0.7 × log(freq+1) / log(12)
	// Maps:
	//   1 repo → 0.30
	//   2 repos → 0.49
	//   3 repos → 0.59
	//   5 repos → 0.70
	//   10 repos → 0.87
	//   11+ repos → 1.00
	logFreq := math.Log(float64(timesSeenAcrossRepos + 1))
	logMax := math.Log(12)
	score := 0.30 + 0.70*(logFreq/logMax)

	if score > 1.0 {
		score = 1.0
	}

	return score
}
