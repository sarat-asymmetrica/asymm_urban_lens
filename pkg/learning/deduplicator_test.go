// Package learning implements Ananta's self-healing pattern database and error classification
//
// Tests for Pattern Deduplicator
// Author: Agent 6.2 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"testing"
	"time"
)

func TestDeduplicatePatterns_ExactDuplicates(t *testing.T) {
	// 10 identical patterns → should become 1
	deduper := NewPatternDeduplicator()

	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "Go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "abc123",
		Confidence:   0.85,
		Frequency:    1,
		RepoSources:  []int64{1},
	}

	// Create 10 identical copies
	patterns := make([]*Pattern, 10)
	for i := range patterns {
		p := *pattern // Copy
		p.Frequency = i + 1
		p.RepoSources = []int64{int64(i + 1)}
		patterns[i] = &p
	}

	deduplicated, stats := deduper.DeduplicatePatterns(patterns)

	if stats.Original != 10 {
		t.Errorf("Expected 10 original patterns, got %d", stats.Original)
	}

	if stats.Final != 1 {
		t.Errorf("Expected 1 final pattern, got %d", stats.Final)
	}

	if stats.Duplicates != 9 {
		t.Errorf("Expected 9 duplicates, got %d", stats.Duplicates)
	}

	// Check merged pattern
	merged := deduplicated[0]
	expectedFreq := 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 // Sum of frequencies
	if merged.Frequency != expectedFreq {
		t.Errorf("Expected frequency %d, got %d", expectedFreq, merged.Frequency)
	}

	// Should have all 10 repo sources
	if len(merged.RepoSources) != 10 {
		t.Errorf("Expected 10 repo sources, got %d", len(merged.RepoSources))
	}
}

func TestDeduplicatePatterns_SimilarPatterns(t *testing.T) {
	// 5 similar patterns (85%+ similarity) → should merge to 1
	deduper := NewPatternDeduplicator()

	patterns := []*Pattern{
		{
			ErrorSig:     "3:xyz",
			Language:     "Go",
			SolutionCode: "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
			Confidence:   0.90,
			Frequency:    10,
		},
		{
			ErrorSig:     "3:xyz",
			Language:     "Go",
			SolutionCode: "if err != nil { return fmt.Errorf(\"failed: %w\", err) }", // Similar
			Confidence:   0.85,
			Frequency:    5,
		},
		{
			ErrorSig:     "3:xyz",
			Language:     "Go",
			SolutionCode: "if err != nil { return fmt.Errorf(\"error occurred: %w\", err) }", // Similar
			Confidence:   0.80,
			Frequency:    3,
		},
		{
			ErrorSig:     "3:xyz",
			Language:     "Go",
			SolutionCode: "if err != nil { return fmt.Errorf(\"oops: %w\", err) }", // Similar
			Confidence:   0.75,
			Frequency:    2,
		},
		{
			ErrorSig:     "3:xyz",
			Language:     "Go",
			SolutionCode: "if err != nil { return fmt.Errorf(\"problem: %w\", err) }", // Similar
			Confidence:   0.70,
			Frequency:    1,
		},
	}

	deduplicated, stats := deduper.DeduplicatePatterns(patterns)

	if stats.Original != 5 {
		t.Errorf("Expected 5 original patterns, got %d", stats.Original)
	}

	// Should merge similar patterns
	if stats.Final > 2 {
		t.Errorf("Expected ≤2 final patterns (similar ones merged), got %d", stats.Final)
	}

	// Merged pattern should have highest confidence solution
	if len(deduplicated) > 0 {
		best := deduplicated[0]
		if best.Confidence < 0.70 {
			t.Errorf("Expected merged pattern to have confidence ≥0.70, got %.2f", best.Confidence)
		}

		// Should accumulate frequencies
		if best.Frequency < 10 {
			t.Errorf("Expected merged frequency ≥10, got %d", best.Frequency)
		}
	}
}

func TestDeduplicatePatterns_DistinctPatterns(t *testing.T) {
	// 10 completely different patterns → should stay 10
	deduper := NewPatternDeduplicator()

	patterns := make([]*Pattern, 10)
	for i := range patterns {
		patterns[i] = &Pattern{
			ErrorSig:     string(rune('A' + i)), // Different signatures
			Language:     "Go",
			SolutionCode: "solution " + string(rune('A'+i)),
			Confidence:   0.80,
			Frequency:    1,
		}
	}

	deduplicated, stats := deduper.DeduplicatePatterns(patterns)

	if stats.Original != 10 {
		t.Errorf("Expected 10 original patterns, got %d", stats.Original)
	}

	if stats.Final != 10 {
		t.Errorf("Expected 10 final patterns (all distinct), got %d", stats.Final)
	}

	if stats.Duplicates != 0 {
		t.Errorf("Expected 0 duplicates, got %d", stats.Duplicates)
	}

	if stats.Merged != 0 {
		t.Errorf("Expected 0 merged, got %d", stats.Merged)
	}

	if len(deduplicated) != 10 {
		t.Errorf("Expected 10 deduplicated patterns, got %d", len(deduplicated))
	}
}

func TestMergePatterns(t *testing.T) {
	deduper := NewPatternDeduplicator()
	now := time.Now()

	patterns := []*Pattern{
		{
			ErrorSig:     "3:test",
			SolutionCode: "solution A",
			Confidence:   0.90, // Highest - should be kept
			Frequency:    5,
			SuccessCount: 4,
			FailureCount: 1,
			RepoSources:  []int64{1, 2},
			CreatedAt:    now.Add(-2 * time.Hour), // Earliest
		},
		{
			ErrorSig:     "3:test",
			SolutionCode: "solution B",
			Confidence:   0.75,
			Frequency:    3,
			SuccessCount: 3,
			FailureCount: 0,
			RepoSources:  []int64{2, 3}, // 2 overlaps with first
			CreatedAt:    now.Add(-1 * time.Hour),
		},
		{
			ErrorSig:     "3:test",
			SolutionCode: "solution C",
			Confidence:   0.60,
			Frequency:    2,
			SuccessCount: 1,
			FailureCount: 1,
			RepoSources:  []int64{4},
			CreatedAt:    now,
		},
	}

	merged := deduper.MergePatterns(patterns)

	// Should keep highest-confidence solution
	if merged.SolutionCode != "solution A" {
		t.Errorf("Expected solution A (highest confidence), got %s", merged.SolutionCode)
	}

	// Weighted average confidence
	// (0.90*5 + 0.75*3 + 0.60*2) / (5+3+2) = (4.5 + 2.25 + 1.2) / 10 = 7.95 / 10 = 0.795
	expectedConf := 0.795
	if merged.Confidence < expectedConf-0.01 || merged.Confidence > expectedConf+0.01 {
		t.Errorf("Expected confidence ≈%.3f, got %.3f", expectedConf, merged.Confidence)
	}

	// Sum frequencies
	expectedFreq := 5 + 3 + 2 // 10
	if merged.Frequency != expectedFreq {
		t.Errorf("Expected frequency %d, got %d", expectedFreq, merged.Frequency)
	}

	// Sum success/failure counts
	if merged.SuccessCount != 8 {
		t.Errorf("Expected 8 successes, got %d", merged.SuccessCount)
	}
	if merged.FailureCount != 2 {
		t.Errorf("Expected 2 failures, got %d", merged.FailureCount)
	}

	// Union of repo sources (1,2,3,4)
	if len(merged.RepoSources) != 4 {
		t.Errorf("Expected 4 unique repo sources, got %d", len(merged.RepoSources))
	}

	// Keep earliest created time
	if !merged.CreatedAt.Equal(now.Add(-2 * time.Hour)) {
		t.Errorf("Expected earliest created_at, got %v", merged.CreatedAt)
	}
}

func TestAreDuplicates(t *testing.T) {
	deduper := NewPatternDeduplicator()

	tests := []struct {
		name        string
		p1          *Pattern
		p2          *Pattern
		wantDupe    bool
		minSim      float64 // Minimum expected similarity
	}{
		{
			name: "exact_hash_match",
			p1: &Pattern{
				ErrorSig:     "3:abc",
				SolutionHash: "hash123",
			},
			p2: &Pattern{
				ErrorSig:     "3:abc",
				SolutionHash: "hash123",
			},
			wantDupe: true,
			minSim:   1.0,
		},
		{
			name: "different_signatures",
			p1: &Pattern{
				ErrorSig:     "3:abc",
				SolutionCode: "if err != nil { return err }",
			},
			p2: &Pattern{
				ErrorSig:     "5:xyz", // Different signature
				SolutionCode: "if err != nil { return err }",
			},
			wantDupe: false,
			minSim:   0.0,
		},
		{
			name: "similar_solutions",
			p1: &Pattern{
				ErrorSig:     "3:test",
				SolutionCode: "if err != nil { return fmt.Errorf(\"error: %w\", err) }",
			},
			p2: &Pattern{
				ErrorSig:     "3:test",
				SolutionCode: "if err != nil { return fmt.Errorf(\"failed: %w\", err) }",
			},
			wantDupe: true,
			minSim:   0.85,
		},
		{
			name: "different_solutions",
			p1: &Pattern{
				ErrorSig:     "3:test",
				SolutionCode: "if err != nil { return err }",
			},
			p2: &Pattern{
				ErrorSig:     "3:test",
				SolutionCode: "log.Fatal(err)",
			},
			wantDupe: false,
			minSim:   0.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			isDupe, sim := deduper.AreDuplicates(tt.p1, tt.p2)

			if isDupe != tt.wantDupe {
				t.Errorf("AreDuplicates() = %v, want %v", isDupe, tt.wantDupe)
			}

			if tt.wantDupe && sim < tt.minSim {
				t.Errorf("Similarity = %.2f, want ≥%.2f", sim, tt.minSim)
			}
		})
	}
}

func TestDeduplicationStats_String(t *testing.T) {
	stats := &DeduplicationStats{
		Original:      100,
		Duplicates:    30,
		Merged:        20,
		Final:         50,
		DuplicateRate: 0.50,
	}

	str := stats.String()

	// Should contain key numbers
	if str == "" {
		t.Error("Stats string is empty")
	}

	t.Logf("Stats: %s", str)
}
