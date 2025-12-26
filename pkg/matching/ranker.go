// Package matching implements quality-based pattern ranking
//
// Ranker: Quality-based pattern ranking and sorting
// Ported from: github.com/asymm_ananta/ananta/internal/learning/ranker.go
// Author: Zen Gardener (Wave 3)
package matching

import (
	"math"
	"sort"
)

// PatternRanker ranks patterns by overall quality score
type PatternRanker struct {
	config MatcherConfig
}

// NewPatternRanker creates a new pattern ranker with default config
func NewPatternRanker() *PatternRanker {
	return &PatternRanker{
		config: DefaultMatcherConfig(),
	}
}

// NewPatternRankerWithConfig creates ranker with custom config
func NewPatternRankerWithConfig(config MatcherConfig) *PatternRanker {
	return &PatternRanker{
		config: config,
	}
}

// RankedPattern pairs a pattern with its computed quality score and rank
type RankedPattern struct {
	Pattern      *Pattern
	QualityScore float64 // Overall quality (0.0-1.0)
	Rank         int     // Rank position (1 = best)
}

// RankPatterns sorts patterns by quality score
//
// Quality formula:
//   quality = confidence × frequency_factor × genericity_factor
//
// Where:
//   - confidence: Base confidence score (from multi-factor scoring)
//   - frequency_factor: log(frequency+1) / log(100)  [rewards usage, diminishing returns]
//   - genericity_factor: placeholder_ratio  [rewards generic solutions]
//
// Returns patterns sorted by quality (best first).
func (pr *PatternRanker) RankPatterns(patterns []*Pattern) []*RankedPattern {
	if len(patterns) == 0 {
		return nil
	}

	// Compute quality scores
	ranked := make([]*RankedPattern, len(patterns))
	for i, p := range patterns {
		ranked[i] = &RankedPattern{
			Pattern:      p,
			QualityScore: pr.CalculateQualityScore(p),
		}
	}

	// Sort by quality score DESC
	sort.Slice(ranked, func(i, j int) bool {
		// Primary: quality score
		if ranked[i].QualityScore != ranked[j].QualityScore {
			return ranked[i].QualityScore > ranked[j].QualityScore
		}
		// Tie-breaker: confidence
		if ranked[i].Pattern.Confidence != ranked[j].Pattern.Confidence {
			return ranked[i].Pattern.Confidence > ranked[j].Pattern.Confidence
		}
		// Tie-breaker: frequency
		return ranked[i].Pattern.Frequency > ranked[j].Pattern.Frequency
	})

	// Assign ranks
	for i := range ranked {
		ranked[i].Rank = i + 1
	}

	return ranked
}

// CalculateQualityScore computes overall pattern quality
//
// Formula:
//   quality = confidence × frequency_factor × genericity_factor
//
// This rewards patterns that are:
//   - High confidence (proven correct)
//   - Frequently used (battle-tested)
//   - Generic (widely applicable)
func (pr *PatternRanker) CalculateQualityScore(pattern *Pattern) float64 {
	if pattern == nil {
		return 0.0
	}

	// Base confidence
	confidence := pattern.Confidence

	// Frequency factor: logarithmic scaling
	// Maps:
	//   1 use → 0.10
	//   5 uses → 0.23
	//   10 uses → 0.30
	//   50 uses → 0.51
	//   100 uses → 0.61
	//   1000+ uses → 1.00
	var frequencyFactor float64
	if pattern.Frequency > 0 {
		frequencyFactor = math.Log(float64(pattern.Frequency+1)) / math.Log(101)
		if frequencyFactor > 1.0 {
			frequencyFactor = 1.0
		}
	} else {
		frequencyFactor = 0.10 // Minimum for untested patterns
	}

	// Genericity factor: ratio of placeholders to total code
	genericityFactor := pr.calculateGenericity(pattern.Template)

	// Combined quality
	quality := confidence * frequencyFactor * genericityFactor

	return quality
}

// calculateGenericity measures how generic a solution is
//
// Genericity = placeholders / (placeholders + literals)
//
// Higher genericity = more reusable across different codebases
func (pr *PatternRanker) calculateGenericity(code string) float64 {
	if code == "" {
		return 0.0
	}

	// Normalize code to count placeholders
	normalized := NormalizeSolution(code)

	// Count placeholders
	placeholders := float64(
		countOccurrences(normalized, "<VAR>") +
			countOccurrences(normalized, "<FUNC>") +
			countOccurrences(normalized, "<TYPE>") +
			countOccurrences(normalized, "<LITERAL>"))

	// Count total tokens (rough estimate)
	tokens := float64(len(splitFields(normalized)))

	if tokens == 0 {
		return 0.0
	}

	// Genericity ratio
	genericity := placeholders / tokens

	// Clamp to [0.1, 1.0]
	// (Even very specific code has some minimal reusability)
	if genericity < 0.1 {
		genericity = 0.1
	}
	if genericity > 1.0 {
		genericity = 1.0
	}

	return genericity
}

// GetTopPatterns returns top N patterns by quality
//
// If n > len(patterns), returns all patterns.
func (pr *PatternRanker) GetTopPatterns(patterns []*Pattern, n int) []*Pattern {
	ranked := pr.RankPatterns(patterns)

	if n > len(ranked) {
		n = len(ranked)
	}

	top := make([]*Pattern, n)
	for i := 0; i < n; i++ {
		top[i] = ranked[i].Pattern
	}

	return top
}

// GetTopPatternsByCategory returns top N patterns for each category
//
// Returns map: category → top patterns
func (pr *PatternRanker) GetTopPatternsByCategory(patterns []*Pattern, n int) map[string][]*Pattern {
	// Group by category
	byCategory := make(map[string][]*Pattern)
	for _, p := range patterns {
		category := p.Category
		if category == "" {
			category = "uncategorized"
		}
		byCategory[category] = append(byCategory[category], p)
	}

	// Get top N for each category
	result := make(map[string][]*Pattern)
	for category, categoryPatterns := range byCategory {
		result[category] = pr.GetTopPatterns(categoryPatterns, n)
	}

	return result
}

// FilterByQuality returns patterns with quality ≥ threshold
//
// threshold: Minimum quality score (0.0-1.0)
func (pr *PatternRanker) FilterByQuality(patterns []*Pattern, threshold float64) []*Pattern {
	var filtered []*Pattern

	for _, p := range patterns {
		if pr.CalculateQualityScore(p) >= threshold {
			filtered = append(filtered, p)
		}
	}

	return filtered
}

// FilterByConfidence returns patterns with confidence ≥ threshold
func (pr *PatternRanker) FilterByConfidence(patterns []*Pattern, threshold float64) []*Pattern {
	var filtered []*Pattern

	for _, p := range patterns {
		if p.Confidence >= threshold {
			filtered = append(filtered, p)
		}
	}

	return filtered
}

// FilterByFrequency returns patterns with frequency ≥ threshold
func (pr *PatternRanker) FilterByFrequency(patterns []*Pattern, threshold int) []*Pattern {
	var filtered []*Pattern

	for _, p := range patterns {
		if p.Frequency >= threshold {
			filtered = append(filtered, p)
		}
	}

	return filtered
}

// FilterByCategory returns patterns matching category
func (pr *PatternRanker) FilterByCategory(patterns []*Pattern, category string) []*Pattern {
	var filtered []*Pattern

	for _, p := range patterns {
		if p.Category == category {
			filtered = append(filtered, p)
		}
	}

	return filtered
}

// FilterByLanguage returns patterns matching language
func (pr *PatternRanker) FilterByLanguage(patterns []*Pattern, language string) []*Pattern {
	var filtered []*Pattern

	for _, p := range patterns {
		if p.Language == language {
			filtered = append(filtered, p)
		}
	}

	return filtered
}

// CombineFilters applies multiple filters in sequence
func (pr *PatternRanker) CombineFilters(patterns []*Pattern, filters ...func([]*Pattern) []*Pattern) []*Pattern {
	result := patterns

	for _, filter := range filters {
		result = filter(result)
		if len(result) == 0 {
			break // No patterns left, stop filtering
		}
	}

	return result
}
