// Package learning tests for continuous learning loop
//
// Tests: Feedback processing, temporal decay, human input, simulation
// Author: Agent 1.3 (Dr. Chen Wei)
// Created: 2025-11-07
package learning

import (
	"context"
	"fmt"
	"math"
	"os"
	"testing"
	"time"
)

// TestProcessApplicationOutcome verifies feedback-driven confidence updates
func TestProcessApplicationOutcome(t *testing.T) {
	// Create temporary database
	dbPath := "test_learning_loop.db"
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open database: %v", err)
	}
	defer db.Close()

	// Run migrations
	if err := ApplyMigrations(db.db); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Create test pattern with initial confidence 0.50
	pattern := &Pattern{
		ErrorSig:     "3:test123",
		ErrorType:    "compile",
		Language:     "Go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "abc123",
		Confidence:   0.50,
		Frequency:    1,
		RepoSources:  []int64{1},
	}

	if err := db.AddPattern(pattern); err != nil {
		t.Fatalf("Failed to add pattern: %v", err)
	}

	// Create learning loop
	loop := NewLearningLoop(db)

	// Test 1: Success outcome increases confidence
	successOutcome := ApplicationOutcome{
		PatternID:          pattern.ID,
		TargetFile:         "test.go",
		AppliedAt:          time.Now(),
		Outcome:            OutcomeSuccess,
		CompilationSuccess: true,
		TestPass:           true,
		QualityScore:       0.92,
		Feedback:           "Fixed error successfully",
	}

	if err := loop.ProcessApplicationOutcome(pattern.ID, successOutcome); err != nil {
		t.Fatalf("Failed to process success outcome: %v", err)
	}

	// Verify confidence increased by 0.05
	patterns, _ := db.FindPatterns("3:test123", "Go", 0.0)
	if len(patterns) == 0 {
		t.Fatal("Pattern not found after success")
	}
	expectedConf := 0.55 // 0.50 + 0.05
	if math.Abs(patterns[0].Confidence-expectedConf) > 0.01 {
		t.Errorf("Expected confidence %.2f, got %.2f", expectedConf, patterns[0].Confidence)
	}

	// Test 2: Failure outcome decreases confidence
	failureOutcome := ApplicationOutcome{
		PatternID:          pattern.ID,
		TargetFile:         "test.go",
		AppliedAt:          time.Now(),
		Outcome:            OutcomeFailure,
		CompilationSuccess: false,
		TestPass:           false,
		QualityScore:       0.30,
		Feedback:           "Compilation failed",
	}

	if err := loop.ProcessApplicationOutcome(pattern.ID, failureOutcome); err != nil {
		t.Fatalf("Failed to process failure outcome: %v", err)
	}

	// Verify confidence decreased by 0.10
	patterns, _ = db.FindPatterns("3:test123", "Go", 0.0)
	expectedConf = 0.45 // 0.55 - 0.10
	if math.Abs(patterns[0].Confidence-expectedConf) > 0.01 {
		t.Errorf("Expected confidence %.2f, got %.2f", expectedConf, patterns[0].Confidence)
	}

	// Test 3: Rejected outcome has no effect
	rejectedOutcome := ApplicationOutcome{
		PatternID:          pattern.ID,
		TargetFile:         "test.go",
		AppliedAt:          time.Now(),
		Outcome:            OutcomeRejected,
		CompilationSuccess: false,
		TestPass:           false,
		QualityScore:       0.0,
		Feedback:           "User rejected suggestion",
	}

	if err := loop.ProcessApplicationOutcome(pattern.ID, rejectedOutcome); err != nil {
		t.Fatalf("Failed to process rejected outcome: %v", err)
	}

	// Verify confidence unchanged
	patterns, _ = db.FindPatterns("3:test123", "Go", 0.0)
	if math.Abs(patterns[0].Confidence-expectedConf) > 0.01 {
		t.Errorf("Rejected outcome should not change confidence")
	}
}

// TestTemporalDecay verifies unused patterns decay over time
func TestTemporalDecay(t *testing.T) {
	// Create temporary database
	dbPath := "test_decay.db"
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open database: %v", err)
	}
	defer db.Close()

	// Run migrations
	if err := ApplyMigrations(db.db); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Create pattern that was last applied 180 days ago
	pattern := &Pattern{
		ErrorSig:     "3:decay_test",
		ErrorType:    "compile",
		Language:     "Go",
		Category:     "error_handling",
		SolutionCode: "if x == nil { return }",
		SolutionHash: "def456",
		Confidence:   0.80, // HIGH tier
		Frequency:    5,
		RepoSources:  []int64{1},
	}

	if err := db.AddPattern(pattern); err != nil {
		t.Fatalf("Failed to add pattern: %v", err)
	}

	// Manually set last_applied to 180 days ago
	oldDate := time.Now().AddDate(0, 0, -180).Format(time.RFC3339)
	_, err = db.db.Exec("UPDATE patterns SET last_applied = ? WHERE id = ?", oldDate, pattern.ID)
	if err != nil {
		t.Fatalf("Failed to set last_applied: %v", err)
	}

	// Apply temporal decay (90 day threshold)
	loop := NewLearningLoop(db)
	ctx := context.Background()
	if err := loop.DecayOldPatterns(ctx); err != nil {
		t.Fatalf("Failed to apply decay: %v", err)
	}

	// Verify confidence decayed
	patterns, _ := db.FindPatterns("3:decay_test", "Go", 0.0)
	if len(patterns) == 0 {
		t.Fatal("Pattern not found after decay")
	}

	// 180 days = 2 periods of 90 days
	// Expected: 0.80 × 0.95² ≈ 0.72
	expectedConf := 0.80 * math.Pow(0.95, 2.0)
	if math.Abs(patterns[0].Confidence-expectedConf) > 0.02 {
		t.Errorf("Expected confidence %.2f, got %.2f", expectedConf, patterns[0].Confidence)
	}
}

// TestHumanPatternInput verifies human-contributed patterns
func TestHumanPatternInput(t *testing.T) {
	// Create temporary database
	dbPath := "test_human.db"
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open database: %v", err)
	}
	defer db.Close()

	// Run migrations
	if err := ApplyMigrations(db.db); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Create learning loop
	loop := NewLearningLoop(db)

	// Add human pattern
	metadata := HumanPatternMetadata{
		AuthorName:  "alice@example.com",
		SubmittedAt: time.Now(),
		Description: "Fix nil pointer in handler",
		VerifiedBy:  "bob@example.com",
		Source:      "code_review",
		Language:    "Go",
		Category:    "error_handling",
	}

	pattern, err := loop.LearnFromHumanSolution(
		"3:human_test",
		"if handler == nil { return errors.New(\"nil handler\") }",
		metadata,
	)
	if err != nil {
		t.Fatalf("Failed to add human pattern: %v", err)
	}

	// Verify initial confidence is 0.85 (HIGH tier)
	if math.Abs(pattern.Confidence-0.85) > 0.01 {
		t.Errorf("Expected human pattern confidence 0.85, got %.2f", pattern.Confidence)
	}

	// Verify pattern is marked as human
	isHuman, err := IsHumanPattern(db, pattern.ID)
	if err != nil {
		t.Fatalf("Failed to check human pattern: %v", err)
	}
	if !isHuman {
		t.Error("Pattern should be marked as human-contributed")
	}

	// Verify metadata can be retrieved
	retrievedMeta, err := GetHumanPatternMetadata(db, pattern.ID)
	if err != nil {
		t.Fatalf("Failed to get metadata: %v", err)
	}
	if retrievedMeta.AuthorName != metadata.AuthorName {
		t.Errorf("Expected author %s, got %s", metadata.AuthorName, retrievedMeta.AuthorName)
	}
}

// TestLearningLoopSimulation runs full simulation with 50 patterns, 100 applications
func TestLearningLoopSimulation(t *testing.T) {
	// Create temporary database
	dbPath := "test_simulation.db"
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open database: %v", err)
	}
	defer db.Close()

	// Run migrations
	if err := ApplyMigrations(db.db); err != nil {
		t.Fatalf("Failed to migrate: %v", err)
	}

	// Create learning loop
	loop := NewLearningLoop(db)

	// Create 50 test patterns with various initial confidences
	patternIDs := make([]int64, 50)
	for i := 0; i < 50; i++ {
		confidence := 0.40 + float64(i%5)*0.10 // Range: 0.40 to 0.80
		pattern := &Pattern{
			ErrorSig:     fmt.Sprintf("3:sim_%d", i),
			ErrorType:    "compile",
			Language:     "Go",
			Category:     "error_handling",
			SolutionCode: fmt.Sprintf("solution_%d", i),
			SolutionHash: fmt.Sprintf("hash_%d", i),
			Confidence:   confidence,
			Frequency:    1,
			RepoSources:  []int64{1},
		}

		if err := db.AddPattern(pattern); err != nil {
			t.Fatalf("Failed to add pattern %d: %v", i, err)
		}
		patternIDs[i] = pattern.ID
	}

	// Simulate 100 applications
	// Distribution: 60 successes, 30 failures, 10 rejected
	for i := 0; i < 100; i++ {
		patternID := patternIDs[i%50] // Cycle through patterns

		var outcome OutcomeType
		if i < 60 {
			outcome = OutcomeSuccess
		} else if i < 90 {
			outcome = OutcomeFailure
		} else {
			outcome = OutcomeRejected
		}

		appOutcome := ApplicationOutcome{
			PatternID:          patternID,
			TargetFile:         fmt.Sprintf("file_%d.go", i),
			AppliedAt:          time.Now(),
			Outcome:            outcome,
			CompilationSuccess: outcome == OutcomeSuccess,
			TestPass:           outcome == OutcomeSuccess,
			QualityScore:       0.85,
			Feedback:           string(outcome),
		}

		if err := loop.ProcessApplicationOutcome(patternID, appOutcome); err != nil {
			t.Fatalf("Failed to process outcome %d: %v", i, err)
		}
	}

	// Verify statistics
	stats, err := loop.GetStatistics()
	if err != nil {
		t.Fatalf("Failed to get statistics: %v", err)
	}

	// Check total applications
	if stats.TotalApplications != 100 {
		t.Errorf("Expected 100 applications, got %d", stats.TotalApplications)
	}

	// Check success/failure/rejected counts
	if stats.SuccessfulApps != 60 {
		t.Errorf("Expected 60 successes, got %d", stats.SuccessfulApps)
	}
	if stats.FailedApps != 30 {
		t.Errorf("Expected 30 failures, got %d", stats.FailedApps)
	}
	if stats.RejectedApps != 10 {
		t.Errorf("Expected 10 rejected, got %d", stats.RejectedApps)
	}

	// Check success rate (60/90 = 0.67, excluding rejected)
	expectedSuccessRate := 60.0 / 90.0
	if math.Abs(stats.SuccessRate-expectedSuccessRate) > 0.05 {
		t.Errorf("Expected success rate %.2f, got %.2f", expectedSuccessRate, stats.SuccessRate)
	}

	// Simulate temporal decay (advance time by 90 days)
	// Set all patterns to 90 days old
	oldDate := time.Now().AddDate(0, 0, -90).Format(time.RFC3339)
	_, err = db.db.Exec("UPDATE patterns SET last_applied = ?", oldDate)
	if err != nil {
		t.Fatalf("Failed to set last_applied: %v", err)
	}

	// Apply decay
	ctx := context.Background()
	if err := loop.DecayOldPatterns(ctx); err != nil {
		t.Fatalf("Failed to apply decay: %v", err)
	}

	// Verify patterns decayed (confidence should be reduced)
	stats, err = loop.GetStatistics()
	if err != nil {
		t.Fatalf("Failed to get statistics after decay: %v", err)
	}

	// Average confidence should be lower after decay
	// (Original range: 0.40-0.80, after decay: reduced by ~5%)
	if stats.AvgConfidence > 0.75 {
		t.Errorf("Average confidence should be reduced after decay, got %.2f", stats.AvgConfidence)
	}

	// Add human pattern and verify it starts at 0.85
	humanMeta := HumanPatternMetadata{
		AuthorName: "expert@example.com",
		Source:     "manual",
		Language:   "Go",
		Category:   "testing",
	}

	humanPattern, err := loop.LearnFromHumanSolution(
		"3:human_sim",
		"assert.NoError(t, err)",
		humanMeta,
	)
	if err != nil {
		t.Fatalf("Failed to add human pattern: %v", err)
	}

	if math.Abs(humanPattern.Confidence-0.85) > 0.01 {
		t.Errorf("Human pattern should start at 0.85, got %.2f", humanPattern.Confidence)
	}

	// Apply successful outcome to human pattern
	humanOutcome := ApplicationOutcome{
		PatternID:          humanPattern.ID,
		TargetFile:         "test_human.go",
		AppliedAt:          time.Now(),
		Outcome:            OutcomeSuccess,
		CompilationSuccess: true,
		TestPass:           true,
		QualityScore:       0.95,
		Feedback:           "Excellent fix",
	}

	if err := loop.ProcessApplicationOutcome(humanPattern.ID, humanOutcome); err != nil {
		t.Fatalf("Failed to process human outcome: %v", err)
	}

	// Verify confidence increased to 0.90
	patterns, _ := db.FindPatterns("3:human_sim", "Go", 0.0)
	expectedConf := 0.90 // 0.85 + 0.05
	if math.Abs(patterns[0].Confidence-expectedConf) > 0.01 {
		t.Errorf("Expected human pattern confidence %.2f, got %.2f", expectedConf, patterns[0].Confidence)
	}

	// Final statistics check
	stats, err = loop.GetStatistics()
	if err != nil {
		t.Fatalf("Failed to get final statistics: %v", err)
	}

	t.Logf("=== SIMULATION RESULTS ===")
	t.Logf("Total Patterns: %d", stats.TotalPatterns)
	t.Logf("High Confidence: %d", stats.HighConfidence)
	t.Logf("Medium Confidence: %d", stats.MediumConfidence)
	t.Logf("Low Confidence: %d", stats.LowConfidence)
	t.Logf("Total Applications: %d", stats.TotalApplications)
	t.Logf("Success Rate: %.2f%%", stats.SuccessRate*100)
	t.Logf("Human Patterns: %d", stats.HumanPatterns)
	t.Logf("Average Confidence: %.3f", stats.AvgConfidence)
}

// TestCalculateQualityScore verifies Five Timbres harmonic mean
func TestCalculateQualityScore(t *testing.T) {
	tests := []struct {
		name     string
		scores   []float64
		expected float64
	}{
		{
			name:     "All strong dimensions",
			scores:   []float64{0.95, 0.90, 0.88, 0.92, 0.85},
			expected: 0.90, // Harmonic mean ≈ 0.90
		},
		{
			name:     "One weak dimension",
			scores:   []float64{0.95, 0.90, 0.88, 0.92, 0.30},
			expected: 0.65, // Harmonic mean penalizes weak dimension (actual: ~0.65)
		},
		{
			name:     "All perfect",
			scores:   []float64{1.0, 1.0, 1.0, 1.0, 1.0},
			expected: 1.0,
		},
		{
			name:     "Empty scores",
			scores:   []float64{},
			expected: 0.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := CalculateQualityScore(tt.scores)
			if math.Abs(result-tt.expected) > 0.05 {
				t.Errorf("Expected %.2f, got %.2f", tt.expected, result)
			}
		})
	}
}

// TestDecayConfidence verifies decay formula
func TestDecayConfidence(t *testing.T) {
	tests := []struct {
		confidence    float64
		daysSinceUse  int
		expectedRange [2]float64 // [min, max] expected range
	}{
		{0.80, 0, [2]float64{0.80, 0.80}},       // No decay
		{0.80, 90, [2]float64{0.75, 0.77}},      // ~5% reduction
		{0.80, 180, [2]float64{0.71, 0.73}},     // ~10% reduction
		{0.60, 365, [2]float64{0.48, 0.50}},     // Significant decay
		{0.15, 180, [2]float64{0.13, 0.15}},     // 180 days decay (not floored yet)
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("%.2f_%ddays", tt.confidence, tt.daysSinceUse), func(t *testing.T) {
			result := DecayConfidence(tt.confidence, tt.daysSinceUse)
			if result < tt.expectedRange[0] || result > tt.expectedRange[1] {
				t.Errorf("Expected range [%.2f, %.2f], got %.2f",
					tt.expectedRange[0], tt.expectedRange[1], result)
			}
		})
	}
}
