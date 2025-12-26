// Package matching implements pattern matching with fuzzy matching
//
// FuzzyMatcher: Multi-tier matching with Vedic optimization
// Author: Zen Gardener (Wave 3)
package matching

import (
	"fmt"
	"math"
	"sort"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/vqc"
)

// FuzzyMatcher implements fuzzy pattern matching with three tiers:
//   Tier 1: Exact matching (hash-based, O(1))
//   Tier 2: Fuzzy matching (Levenshtein + digital root, O(n))
//   Tier 3: Semantic matching (quaternion similarity, O(n))
type FuzzyMatcher struct {
	config MatcherConfig
}

// NewFuzzyMatcher creates a new fuzzy matcher with default config
func NewFuzzyMatcher() *FuzzyMatcher {
	return &FuzzyMatcher{
		config: DefaultMatcherConfig(),
	}
}

// NewFuzzyMatcherWithConfig creates a fuzzy matcher with custom config
func NewFuzzyMatcherWithConfig(config MatcherConfig) *FuzzyMatcher {
	return &FuzzyMatcher{
		config: config,
	}
}

// Match finds all matching patterns for input
func (fm *FuzzyMatcher) Match(input interface{}, patterns []Pattern) ([]Match, error) {
	startTime := time.Now()

	// Convert input to string
	inputStr, ok := input.(string)
	if !ok {
		return nil, fmt.Errorf("input must be string, got %T", input)
	}

	// Encode input to quaternion
	inputQ := EncodeToQuaternion(inputStr)
	inputHash := HashContent(inputStr)

	// TIER 1: Exact matching (O(1) per pattern)
	var matches []Match
	exactMatches := fm.findExactMatches(inputStr, inputHash, patterns)
	matches = append(matches, exactMatches...)

	// If we have exact matches above threshold, return early
	if len(exactMatches) > 0 && exactMatches[0].Score >= fm.config.ExactMatchThreshold {
		for i := range matches {
			matches[i].Context.ComputeTimeNs = time.Since(startTime).Nanoseconds()
			matches[i].Context.AlgorithmUsed = "exact"
		}
		return matches, nil
	}

	// TIER 2: Fuzzy matching with digital root pre-filter
	fuzzyMatches := fm.findFuzzyMatches(inputStr, inputQ, patterns)
	matches = append(matches, fuzzyMatches...)

	// TIER 3: Semantic matching (quaternion similarity)
	// Only if we don't have enough high-quality fuzzy matches
	if len(fuzzyMatches) == 0 || fuzzyMatches[0].Score < fm.config.FuzzyMatchThreshold {
		semanticMatches := fm.findSemanticMatches(inputStr, inputQ, patterns)
		matches = append(matches, semanticMatches...)
	}

	// Filter by minimum similarity
	var filtered []Match
	for _, m := range matches {
		if m.Score >= fm.config.MinSimilarity {
			m.Context.ComputeTimeNs = time.Since(startTime).Nanoseconds()
			filtered = append(filtered, m)
		}
	}

	// Sort by score DESC
	sort.Slice(filtered, func(i, j int) bool {
		return filtered[i].Score > filtered[j].Score
	})

	return filtered, nil
}

// BestMatch finds the single best match
func (fm *FuzzyMatcher) BestMatch(input interface{}, patterns []Pattern) (*Match, error) {
	matches, err := fm.Match(input, patterns)
	if err != nil {
		return nil, err
	}

	if len(matches) == 0 {
		return nil, fmt.Errorf("no matches found")
	}

	// Return highest scoring match
	best := matches[0]
	return &best, nil
}

// MatchWithContext matches with additional context
func (fm *FuzzyMatcher) MatchWithContext(input interface{}, patterns []Pattern, ctx MatchContext) ([]Match, error) {
	matches, err := fm.Match(input, patterns)
	if err != nil {
		return nil, err
	}

	// Enhance matches with provided context
	for i := range matches {
		matches[i].Context.Metadata = ctx.Metadata
		matches[i].Context.QuaternionState = ctx.QuaternionState
	}

	return matches, nil
}

// RankMatches ranks matches by quality
func (fm *FuzzyMatcher) RankMatches(matches []Match) []RankedMatch {
	if len(matches) == 0 {
		return nil
	}

	ranked := make([]RankedMatch, len(matches))
	for i, m := range matches {
		quality := fm.calculateQualityScore(&m)
		ranked[i] = RankedMatch{
			Match:        &matches[i],
			QualityScore: quality,
		}
	}

	// Sort by quality DESC
	sort.Slice(ranked, func(i, j int) bool {
		if ranked[i].QualityScore != ranked[j].QualityScore {
			return ranked[i].QualityScore > ranked[j].QualityScore
		}
		// Tie-breaker: match score
		if ranked[i].Match.Score != ranked[j].Match.Score {
			return ranked[i].Match.Score > ranked[j].Match.Score
		}
		// Tie-breaker: confidence
		return ranked[i].Match.Confidence > ranked[j].Match.Confidence
	})

	// Assign ranks
	for i := range ranked {
		ranked[i].Rank = i + 1
		ranked[i].Match.Rank = i + 1
	}

	return ranked
}

// findExactMatches finds patterns with exact hash match (O(1) per pattern)
func (fm *FuzzyMatcher) findExactMatches(input, inputHash string, patterns []Pattern) []Match {
	var matches []Match

	for _, p := range patterns {
		if p.Hash == inputHash {
			matches = append(matches, Match{
				Pattern:     &p,
				Score:       1.0,
				Bindings:    make(map[string]interface{}),
				Context:     MatchContext{InputHash: inputHash, AlgorithmUsed: "exact"},
				Explanation: "Exact hash match",
				Confidence:  p.Confidence,
			})
		}
	}

	return matches
}

// findFuzzyMatches finds patterns with fuzzy similarity (with digital root pre-filter)
func (fm *FuzzyMatcher) findFuzzyMatches(input string, inputQ vqc.Quaternion, patterns []Pattern) []Match {
	var matches []Match

	inputDR := vqc.DigitalRoot(len(input))
	normalizedInput := NormalizeSolution(input)

	for _, p := range patterns {
		// PHASE 1: Digital root pre-filter (88.9% elimination!)
		if fm.config.UseDigitalRootFilter {
			patternDR := vqc.DigitalRoot(len(p.Template))
			if inputDR != patternDR {
				continue // Skip this pattern (digital root mismatch)
			}
		}

		// PHASE 2: Structural similarity
		normalizedPattern := NormalizeSolution(p.Template)
		structural := StructuralSimilarity(normalizedInput, normalizedPattern)

		if structural >= fm.config.FuzzyMatchThreshold {
			matches = append(matches, Match{
				Pattern:     &p,
				Score:       structural,
				Bindings:    make(map[string]interface{}),
				Context:     MatchContext{InputHash: HashContent(input), AlgorithmUsed: "fuzzy"},
				Explanation: fmt.Sprintf("Fuzzy match (%.1f%% structural similarity)", structural*100),
				Confidence:  p.Confidence * structural,
			})
		}
	}

	return matches
}

// findSemanticMatches finds patterns with quaternion similarity
func (fm *FuzzyMatcher) findSemanticMatches(input string, inputQ vqc.Quaternion, patterns []Pattern) []Match {
	var matches []Match

	for _, p := range patterns {
		// Quaternion similarity
		qSim := QuaternionSimilarity(inputQ, p.State)

		if qSim >= fm.config.MinSimilarity {
			matches = append(matches, Match{
				Pattern:     &p,
				Score:       qSim,
				Bindings:    make(map[string]interface{}),
				Context:     MatchContext{InputHash: HashContent(input), AlgorithmUsed: "semantic"},
				Explanation: fmt.Sprintf("Semantic match (%.1f%% quaternion similarity)", qSim*100),
				Confidence:  p.Confidence * qSim,
			})
		}
	}

	return matches
}

// calculateQualityScore computes overall pattern quality
//
// Formula (from Ananta ranker.go):
//   quality = confidence × frequency_factor × genericity_factor
func (fm *FuzzyMatcher) calculateQualityScore(match *Match) float64 {
	if match == nil || match.Pattern == nil {
		return 0.0
	}

	p := match.Pattern

	// Base confidence (from match)
	confidence := match.Confidence

	// Frequency factor: logarithmic scaling
	// Maps:
	//   1 use → 0.10
	//   10 uses → 0.30
	//   50 uses → 0.51
	//   100 uses → 0.61
	//   1000+ uses → 1.00
	var frequencyFactor float64
	if p.Frequency > 0 {
		frequencyFactor = math.Log(float64(p.Frequency+1)) / math.Log(101)
		if frequencyFactor > 1.0 {
			frequencyFactor = 1.0
		}
	} else {
		frequencyFactor = 0.10 // Minimum for untested patterns
	}

	// Genericity factor: ratio of placeholders to total code
	genericityFactor := fm.calculateGenericity(p.Template)

	// Combined quality
	quality := confidence * frequencyFactor * genericityFactor

	return quality
}

// calculateGenericity measures how generic a solution is
// Genericity = placeholders / (placeholders + literals)
func (fm *FuzzyMatcher) calculateGenericity(code string) float64 {
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
	if genericity < 0.1 {
		genericity = 0.1
	}
	if genericity > 1.0 {
		genericity = 1.0
	}

	return genericity
}

// GetTopPatterns returns top N matches by quality
func (fm *FuzzyMatcher) GetTopPatterns(matches []Match, n int) []Match {
	ranked := fm.RankMatches(matches)

	if n > len(ranked) {
		n = len(ranked)
	}

	top := make([]Match, n)
	for i := 0; i < n; i++ {
		top[i] = *ranked[i].Match
	}

	return top
}

// countOccurrences counts occurrences of substring in string
func countOccurrences(s, substr string) int {
	count := 0
	for i := 0; i <= len(s)-len(substr); {
		if s[i:i+len(substr)] == substr {
			count++
			i += len(substr)
		} else {
			i++
		}
	}
	return count
}

// splitFields splits string into fields (whitespace-separated)
func splitFields(s string) []string {
	var fields []string
	field := ""
	for _, r := range s {
		if r == ' ' || r == '\t' || r == '\n' {
			if field != "" {
				fields = append(fields, field)
				field = ""
			}
		} else {
			field += string(r)
		}
	}
	if field != "" {
		fields = append(fields, field)
	}
	return fields
}
