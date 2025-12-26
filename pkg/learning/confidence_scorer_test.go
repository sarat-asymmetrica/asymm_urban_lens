// Package learning implements Ananta's self-healing pattern database and error classification
//
// Tests for Confidence Scorer
// Author: Agent 6.2 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"testing"
)

func TestScorePattern(t *testing.T) {
	scorer := NewConfidenceScorer()

	tests := []struct {
		name     string
		pattern  *Pattern
		context  ScoringContext
		minScore float64 // Minimum expected score
		maxScore float64 // Maximum expected score
	}{
		{
			name: "high_quality_pattern",
			pattern: &Pattern{
				SolutionCode: "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
			},
			context: ScoringContext{
				RepoStars:            10000, // High star repo
				CommitMessage:        "Fix: Handle error correctly (#123)",
				TimesSeenAcrossRepos: 5,
				SolutionComplexity:   50,
				TotalRepos:           10,
			},
			minScore: 0.70,
			maxScore: 1.00,
		},
		{
			name: "low_quality_pattern",
			pattern: &Pattern{
				SolutionCode: "// TODO: fix this",
			},
			context: ScoringContext{
				RepoStars:            10,
				CommitMessage:        "wip",
				TimesSeenAcrossRepos: 1,
				SolutionComplexity:   10,
				TotalRepos:           10,
			},
			minScore: 0.00,
			maxScore: 0.40,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := scorer.ScorePattern(tt.pattern, tt.context)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("Score %.3f not in range [%.3f, %.3f]", score, tt.minScore, tt.maxScore)
			}

			t.Logf("Pattern score: %.3f", score)
		})
	}
}

func TestCalculateRepoScore(t *testing.T) {
	scorer := NewConfidenceScorer()

	tests := []struct {
		stars    int
		minScore float64
		maxScore float64
	}{
		{stars: 0, minScore: 0.10, maxScore: 0.10},
		{stars: 100, minScore: 0.45, maxScore: 0.55},
		{stars: 1000, minScore: 0.65, maxScore: 0.75},
		{stars: 10000, minScore: 0.85, maxScore: 0.95},
		{stars: 50000, minScore: 0.95, maxScore: 1.00},
	}

	for _, tt := range tests {
		t.Run("stars="+string(rune(tt.stars)), func(t *testing.T) {
			score := scorer.CalculateRepoScore(tt.stars)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("RepoScore(%d) = %.3f, want [%.3f, %.3f]", tt.stars, score, tt.minScore, tt.maxScore)
			}
		})
	}
}

func TestCalculateCommitScore(t *testing.T) {
	scorer := NewConfidenceScorer()

	tests := []struct {
		name     string
		message  string
		minScore float64
		maxScore float64
	}{
		{
			name:     "excellent_commit",
			message:  "Fix: Handle nil pointer error in database connection (#142)",
			minScore: 0.70,
			maxScore: 1.00,
		},
		{
			name:     "good_commit",
			message:  "Fixed error handling in user authentication",
			minScore: 0.50,
			maxScore: 0.80,
		},
		{
			name:     "neutral_commit",
			message:  "Update code",
			minScore: 0.20,
			maxScore: 0.50,
		},
		{
			name:     "bad_commit",
			message:  "wip",
			minScore: 0.00,
			maxScore: 0.30,
		},
		{
			name:     "terrible_commit",
			message:  "TODO test tmp",
			minScore: 0.00,
			maxScore: 0.20,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := scorer.CalculateCommitScore(tt.message)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("CommitScore(%q) = %.3f, want [%.3f, %.3f]", tt.message, score, tt.minScore, tt.maxScore)
			}

			t.Logf("Commit '%s' score: %.3f", tt.message, score)
		})
	}
}

func TestCalculateSolutionScore(t *testing.T) {
	scorer := NewConfidenceScorer()

	tests := []struct {
		name     string
		solution string
		minScore float64
		maxScore float64
	}{
		{
			name:     "generic_solution",
			solution: "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
			minScore: 0.60,
			maxScore: 1.00,
		},
		{
			name:     "specific_solution",
			solution: "if myappError != nil { return myappError }",
			minScore: 0.20,
			maxScore: 0.70,
		},
		{
			name:     "too_simple",
			solution: "return",
			minScore: 0.00,
			maxScore: 0.40,
		},
		{
			name:     "empty_solution",
			solution: "",
			minScore: 0.00,
			maxScore: 0.00,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := scorer.CalculateSolutionScore(tt.solution)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("SolutionScore(%q) = %.3f, want [%.3f, %.3f]", tt.solution, score, tt.minScore, tt.maxScore)
			}

			t.Logf("Solution score: %.3f", score)
		})
	}
}

func TestCalculateFrequencyScore(t *testing.T) {
	scorer := NewConfidenceScorer()

	tests := []struct {
		timesSeenAcrossRepos int
		totalRepos           int
		minScore             float64
		maxScore             float64
	}{
		{timesSeenAcrossRepos: 1, totalRepos: 10, minScore: 0.30, maxScore: 0.30},
		{timesSeenAcrossRepos: 3, totalRepos: 10, minScore: 0.50, maxScore: 0.65},
		{timesSeenAcrossRepos: 5, totalRepos: 10, minScore: 0.65, maxScore: 0.75},
		{timesSeenAcrossRepos: 10, totalRepos: 10, minScore: 0.80, maxScore: 0.95},
		{timesSeenAcrossRepos: 11, totalRepos: 10, minScore: 0.95, maxScore: 1.00},
	}

	for _, tt := range tests {
		t.Run("freq="+string(rune(tt.timesSeenAcrossRepos)), func(t *testing.T) {
			score := scorer.CalculateFrequencyScore(tt.timesSeenAcrossRepos, tt.totalRepos)

			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("FrequencyScore(%d, %d) = %.3f, want [%.3f, %.3f]",
					tt.timesSeenAcrossRepos, tt.totalRepos, score, tt.minScore, tt.maxScore)
			}
		})
	}
}
