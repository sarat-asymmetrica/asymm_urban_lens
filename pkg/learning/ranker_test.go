// Package learning implements Ananta's self-healing pattern database and error classification
//
// Tests for Pattern Ranker
// Author: Agent 6.2 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"testing"
)

func TestRankPatterns(t *testing.T) {
	ranker := NewPatternRanker()

	patterns := []*Pattern{
		{
			ErrorSig:     "1:low",
			SolutionCode: "return nil",
			Confidence:   0.50,
			Frequency:    1,
		},
		{
			ErrorSig:     "2:high",
			SolutionCode: "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
			Confidence:   0.90,
			Frequency:    100,
		},
		{
			ErrorSig:     "3:medium",
			SolutionCode: "return err",
			Confidence:   0.70,
			Frequency:    10,
		},
	}

	ranked := ranker.RankPatterns(patterns)

	if len(ranked) != 3 {
		t.Fatalf("Expected 3 ranked patterns, got %d", len(ranked))
	}

	// Check ranking order (best first)
	if ranked[0].Rank != 1 {
		t.Errorf("Expected rank 1 for first pattern, got %d", ranked[0].Rank)
	}

	// Highest quality should be first
	if ranked[0].Pattern.ErrorSig != "2:high" {
		t.Errorf("Expected high-quality pattern first, got %s", ranked[0].Pattern.ErrorSig)
	}

	// Verify descending quality
	for i := 1; i < len(ranked); i++ {
		if ranked[i].QualityScore > ranked[i-1].QualityScore {
			t.Errorf("Quality not descending: rank %d (%.3f) > rank %d (%.3f)",
				ranked[i].Rank, ranked[i].QualityScore,
				ranked[i-1].Rank, ranked[i-1].QualityScore)
		}
	}

	t.Logf("Ranking:")
	for _, rp := range ranked {
		t.Logf("  #%d: %s (quality=%.3f, conf=%.3f, freq=%d)",
			rp.Rank, rp.Pattern.ErrorSig, rp.QualityScore, rp.Pattern.Confidence, rp.Pattern.Frequency)
	}
}

func TestPatternRanker_CalculateQualityScore(t *testing.T) {
	ranker := NewPatternRanker()

	tests := []struct {
		name     string
		pattern  *Pattern
		minScore float64
		maxScore float64
	}{
		{
			name: "excellent_pattern",
			pattern: &Pattern{
				SolutionCode: "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
				Confidence:   0.95,
				Frequency:    100,
			},
			minScore: 0.50,
			maxScore: 1.00,
		},
		{
			name: "good_pattern",
			pattern: &Pattern{
				SolutionCode: "return err",
				Confidence:   0.80,
				Frequency:    20,
			},
			minScore: 0.30,
			maxScore: 0.70,
		},
		{
			name: "poor_pattern",
			pattern: &Pattern{
				SolutionCode: "x",
				Confidence:   0.40,
				Frequency:    1,
			},
			minScore: 0.00,
			maxScore: 0.30,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := ranker.CalculateQualityScore(tt.pattern)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("QualityScore = %.3f, want [%.3f, %.3f]", score, tt.minScore, tt.maxScore)
			}

			t.Logf("Quality score: %.3f", score)
		})
	}
}

func TestGetTopPatterns(t *testing.T) {
	ranker := NewPatternRanker()

	// Create 10 patterns with different qualities
	patterns := make([]*Pattern, 10)
	for i := range patterns {
		patterns[i] = &Pattern{
			ErrorSig:   string(rune('A' + i)),
			Confidence: float64(i+1) / 10.0, // 0.1, 0.2, ..., 1.0
			Frequency:  i + 1,
		}
	}

	// Get top 3
	top := ranker.GetTopPatterns(patterns, 3)

	if len(top) != 3 {
		t.Fatalf("Expected 3 top patterns, got %d", len(top))
	}

	// Should be highest quality patterns
	for i := 1; i < len(top); i++ {
		score1 := ranker.CalculateQualityScore(top[i-1])
		score2 := ranker.CalculateQualityScore(top[i])

		if score2 > score1 {
			t.Errorf("Top patterns not in descending order: %.3f < %.3f", score1, score2)
		}
	}

	t.Logf("Top 3 patterns: %v", top)
}

func TestGetTopPatternsByCategory(t *testing.T) {
	ranker := NewPatternRanker()

	patterns := []*Pattern{
		{ErrorSig: "1", Category: "error_handling", Confidence: 0.90, Frequency: 10},
		{ErrorSig: "2", Category: "error_handling", Confidence: 0.80, Frequency: 5},
		{ErrorSig: "3", Category: "nil_check", Confidence: 0.85, Frequency: 8},
		{ErrorSig: "4", Category: "nil_check", Confidence: 0.75, Frequency: 3},
		{ErrorSig: "5", Category: "type_assertion", Confidence: 0.88, Frequency: 12},
	}

	topByCategory := ranker.GetTopPatternsByCategory(patterns, 2)

	// Should have 3 categories
	if len(topByCategory) != 3 {
		t.Errorf("Expected 3 categories, got %d", len(topByCategory))
	}

	// Each category should have ≤2 patterns
	for category, patterns := range topByCategory {
		if len(patterns) > 2 {
			t.Errorf("Category %s has %d patterns, want ≤2", category, len(patterns))
		}

		t.Logf("Category %s: %d patterns", category, len(patterns))
	}
}

func TestFilterByQuality(t *testing.T) {
	ranker := NewPatternRanker()

	patterns := []*Pattern{
		{ErrorSig: "1", SolutionCode: "good solution", Confidence: 0.90, Frequency: 100},
		{ErrorSig: "2", SolutionCode: "ok solution", Confidence: 0.70, Frequency: 10},
		{ErrorSig: "3", SolutionCode: "poor solution", Confidence: 0.40, Frequency: 1},
	}

	// Filter for quality ≥ 0.50
	filtered := ranker.FilterByQuality(patterns, 0.50)

	// Should filter out low-quality patterns
	if len(filtered) == len(patterns) {
		t.Error("FilterByQuality did not filter any patterns")
	}

	// All filtered patterns should meet threshold
	for _, p := range filtered {
		quality := ranker.CalculateQualityScore(p)
		if quality < 0.50 {
			t.Errorf("Pattern %s has quality %.3f < 0.50", p.ErrorSig, quality)
		}
	}

	t.Logf("Filtered %d/%d patterns with quality ≥ 0.50", len(filtered), len(patterns))
}

func TestCalculateGenericity(t *testing.T) {
	ranker := NewPatternRanker()

	tests := []struct {
		name     string
		code     string
		minScore float64
		maxScore float64
	}{
		{
			name:     "generic_code",
			code:     "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
			minScore: 0.30,
			maxScore: 0.80,
		},
		{
			name:     "specific_code",
			code:     "myAppSpecificFunction(myAppVariable)",
			minScore: 0.10,
			maxScore: 0.50,
		},
		{
			name:     "empty_code",
			code:     "",
			minScore: 0.00,
			maxScore: 0.00,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := ranker.calculateGenericity(tt.code)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("Genericity = %.3f, want [%.3f, %.3f]", score, tt.minScore, tt.maxScore)
			}

			t.Logf("Genericity: %.3f", score)
		})
	}
}
