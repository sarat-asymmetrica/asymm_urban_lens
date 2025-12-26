// Package learning implements Ananta's self-healing pattern database and error classification
//
// Tests for Pattern Merger
// Author: Agent 6.2 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestMergePatterns_NewPatterns(t *testing.T) {
	// Create test database
	dbPath := filepath.Join(os.TempDir(), "test_merge_new.db")
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open DB: %v", err)
	}
	defer db.Close()

	// Migrate
	schema := getTestSchema()
	if err := db.Migrate(schema); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Create merger
	merger := NewPatternMerger(db)

	// Add new patterns
	newPatterns := []*Pattern{
		{
			ErrorSig:     "1:abc",
			ErrorType:    "compile",
			Language:     "Go",
			SolutionCode: "return nil",
			Confidence:   0.85,
			Frequency:    1,
		},
		{
			ErrorSig:     "2:def",
			ErrorType:    "compile",
			Language:     "Go",
			SolutionCode: "return err",
			Confidence:   0.90,
			Frequency:    1,
		},
	}

	stats, err := merger.MergePatterns(newPatterns)
	if err != nil {
		t.Fatalf("MergePatterns failed: %v", err)
	}

	if stats.NewPatterns != 2 {
		t.Errorf("Expected 2 new patterns, got %d", stats.NewPatterns)
	}

	if stats.UpdatedPatterns != 0 {
		t.Errorf("Expected 0 updated patterns, got %d", stats.UpdatedPatterns)
	}

	if stats.SkippedPatterns != 0 {
		t.Errorf("Expected 0 skipped patterns, got %d", stats.SkippedPatterns)
	}

	t.Logf("Merge stats: %s", stats.String())
}

func TestMergePatterns_UpdateExisting(t *testing.T) {
	// Create test database
	dbPath := filepath.Join(os.TempDir(), "test_merge_update.db")
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open DB: %v", err)
	}
	defer db.Close()

	// Migrate
	schema := getTestSchema()
	if err := db.Migrate(schema); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Add existing pattern
	existing := &Pattern{
		ErrorSig:     "3:xyz",
		ErrorType:    "compile",
		Language:     "Go",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.80,
		Frequency:    5,
		SuccessCount: 4,
		RepoSources:  []int64{1, 2},
	}

	if err := db.AddPattern(existing); err != nil {
		t.Fatalf("Failed to add existing pattern: %v", err)
	}

	// Create merger
	merger := NewPatternMerger(db)

	// Add similar pattern (should update existing)
	newPatterns := []*Pattern{
		{
			ErrorSig:     "3:xyz",
			ErrorType:    "compile",
			Language:     "Go",
			SolutionCode: "if err != nil { return err }",
			SolutionHash: "hash123",
			Confidence:   0.85,
			Frequency:    3,
			SuccessCount: 3,
			RepoSources:  []int64{3, 4},
		},
	}

	stats, err := merger.MergePatterns(newPatterns)
	if err != nil {
		t.Fatalf("MergePatterns failed: %v", err)
	}

	if stats.NewPatterns != 0 {
		t.Errorf("Expected 0 new patterns, got %d", stats.NewPatterns)
	}

	if stats.UpdatedPatterns != 1 {
		t.Errorf("Expected 1 updated pattern, got %d", stats.UpdatedPatterns)
	}

	// Verify merged pattern
	patterns, err := db.FindPatterns("3:xyz", "Go", 0.0)
	if err != nil {
		t.Fatalf("Failed to find patterns: %v", err)
	}

	if len(patterns) != 1 {
		t.Fatalf("Expected 1 pattern, got %d", len(patterns))
	}

	merged := patterns[0]

	// Should have combined frequency
	if merged.Frequency != 8 {
		t.Errorf("Expected frequency 8 (5+3), got %d", merged.Frequency)
	}

	// Should have combined success count
	if merged.SuccessCount != 7 {
		t.Errorf("Expected success count 7 (4+3), got %d", merged.SuccessCount)
	}

	// Should have union of repo sources (1,2,3,4)
	if len(merged.RepoSources) != 4 {
		t.Errorf("Expected 4 repo sources, got %d", len(merged.RepoSources))
	}
}

func TestMergePatterns_SkipLowConfidence(t *testing.T) {
	// Create test database
	dbPath := filepath.Join(os.TempDir(), "test_merge_skip.db")
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open DB: %v", err)
	}
	defer db.Close()

	// Migrate
	schema := getTestSchema()
	if err := db.Migrate(schema); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Create merger
	merger := NewPatternMerger(db)

	// Add patterns with very low confidence
	newPatterns := []*Pattern{
		{
			ErrorSig:   "1:low",
			Language:   "Go",
			Confidence: 0.10, // Below 0.30 threshold
		},
		{
			ErrorSig:   "2:low",
			Language:   "Go",
			Confidence: 0.20, // Below threshold
		},
	}

	stats, err := merger.MergePatterns(newPatterns)
	if err != nil {
		t.Fatalf("MergePatterns failed: %v", err)
	}

	if stats.SkippedPatterns != 2 {
		t.Errorf("Expected 2 skipped patterns, got %d", stats.SkippedPatterns)
	}
}

func TestUpdateExistingPattern(t *testing.T) {
	merger := NewPatternMerger(nil) // Don't need DB for this test
	now := time.Now()

	existing := &Pattern{
		ID:           1,
		ErrorSig:     "3:test",
		SolutionCode: "solution A",
		Confidence:   0.70,
		Frequency:    5,
		SuccessCount: 4,
		FailureCount: 1,
		RepoSources:  []int64{1, 2},
		CreatedAt:    now.Add(-1 * time.Hour),
		LastApplied:  now.Add(-30 * time.Minute),
	}

	new := &Pattern{
		ErrorSig:     "3:test",
		SolutionCode: "solution B",
		Confidence:   0.90, // Higher confidence
		Frequency:    3,
		SuccessCount: 3,
		FailureCount: 0,
		RepoSources:  []int64{2, 3},
		CreatedAt:    now,
		LastApplied:  now,
	}

	updated := merger.UpdateExistingPattern(existing, new)

	// Should keep existing ID
	if updated.ID != 1 {
		t.Errorf("Expected ID=1, got %d", updated.ID)
	}

	// Should use higher-confidence solution
	if updated.SolutionCode != "solution B" {
		t.Errorf("Expected solution B, got %s", updated.SolutionCode)
	}

	// Weighted average confidence
	// (0.70*5 + 0.90*3) / (5+3) = (3.5 + 2.7) / 8 = 6.2 / 8 = 0.775
	expectedConf := 0.775
	if updated.Confidence < expectedConf-0.01 || updated.Confidence > expectedConf+0.01 {
		t.Errorf("Expected confidence ≈%.3f, got %.3f", expectedConf, updated.Confidence)
	}

	// Combined frequency
	if updated.Frequency != 8 {
		t.Errorf("Expected frequency 8, got %d", updated.Frequency)
	}

	// Combined success/failure
	if updated.SuccessCount != 7 {
		t.Errorf("Expected 7 successes, got %d", updated.SuccessCount)
	}
	if updated.FailureCount != 1 {
		t.Errorf("Expected 1 failure, got %d", updated.FailureCount)
	}

	// Union of repo sources (1,2,3)
	if len(updated.RepoSources) != 3 {
		t.Errorf("Expected 3 repo sources, got %d", len(updated.RepoSources))
	}

	// Keep original creation time
	if !updated.CreatedAt.Equal(existing.CreatedAt) {
		t.Errorf("Expected original created_at, got %v", updated.CreatedAt)
	}

	// Keep most recent LastApplied
	if !updated.LastApplied.Equal(new.LastApplied) {
		t.Errorf("Expected most recent last_applied, got %v", updated.LastApplied)
	}
}

func getTestSchema() string {
	return `
CREATE TABLE IF NOT EXISTS patterns (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    error_signature TEXT NOT NULL,
    error_type TEXT NOT NULL,
    language TEXT NOT NULL,
    category TEXT,
    solution_code TEXT NOT NULL,
    solution_hash TEXT,
    confidence REAL DEFAULT 0.5,
    frequency INTEGER DEFAULT 1,
    last_applied TEXT,
    success_count INTEGER DEFAULT 0,
    failure_count INTEGER DEFAULT 0,
    repo_sources TEXT DEFAULT '[]',
    created_at TEXT DEFAULT (datetime('now')),
    updated_at TEXT DEFAULT (datetime('now')),
    UNIQUE(error_signature, language)
);
`
}
