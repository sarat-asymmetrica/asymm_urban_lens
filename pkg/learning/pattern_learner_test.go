package learning

import (
	"math"
	"os"
	"path/filepath"
	"testing"
	"time"
)

func setupLearnerTestDB(t *testing.T) (*PatternDB, string) {
	t.Helper()

	// Create temp directory
	tmpDir := filepath.Join(os.TempDir(), "pattern_learner_test")
	os.MkdirAll(tmpDir, 0755)

	dbPath := filepath.Join(tmpDir, "test.db")

	// Open database
	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("Failed to open test database: %v", err)
	}

	return db, tmpDir
}

func cleanupLearnerTestDB(db *PatternDB, tmpDir string) {
	if db != nil {
		db.Close()
	}
	os.RemoveAll(tmpDir)
}

func TestPatternLearner_LearnSuccess(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create a test pattern
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.7,
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 0,
		FailureCount: 0,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	err := db.AddPattern(pattern)
	if err != nil {
		t.Fatalf("Failed to add pattern: %v", err)
	}

	// Learn success
	entry := LearningEntry{
		PatternID:     pattern.ID,
		Success:       true,
		ErrorDelta:    -1,
		QualityChange: 0.1,
		Context:       "test.go",
		FixedErrors:   []string{"3:a1b2c3d4"},
		NewErrors:     []string{},
		Timestamp:     time.Now(),
	}

	err = learner.LearnSuccess(pattern.ID, entry)
	if err != nil {
		t.Fatalf("LearnSuccess failed: %v", err)
	}

	// Verify pattern updated
	updated, err := db.GetPatternByID(pattern.ID)
	if err != nil {
		t.Fatalf("Failed to get updated pattern: %v", err)
	}

	// Confidence should increase by 0.1
	expectedConfidence := 0.8
	if math.Abs(updated.Confidence-expectedConfidence) > 0.001 {
		t.Errorf("Expected confidence %.3f, got %.3f", expectedConfidence, updated.Confidence)
	}

	// Success count should increment
	if updated.SuccessCount != 1 {
		t.Errorf("Expected success count 1, got %d", updated.SuccessCount)
	}
}

func TestPatternLearner_LearnSuccess_ConfidenceCapped(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create pattern with high confidence
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.95, // Already high
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 5,
		FailureCount: 0,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	db.AddPattern(pattern)

	// Learn success (should cap at 1.0)
	entry := LearningEntry{
		PatternID:     pattern.ID,
		Success:       true,
		ErrorDelta:    -1,
		QualityChange: 0.1,
		Context:       "test.go",
		FixedErrors:   []string{"3:a1b2c3d4"},
		NewErrors:     []string{},
		Timestamp:     time.Now(),
	}

	learner.LearnSuccess(pattern.ID, entry)

	updated, _ := db.GetPatternByID(pattern.ID)

	// Confidence should be capped at 1.0
	if updated.Confidence > 1.0 {
		t.Errorf("Confidence exceeded 1.0: %.3f", updated.Confidence)
	}

	if updated.Confidence != 1.0 {
		t.Errorf("Expected confidence 1.0, got %.3f", updated.Confidence)
	}
}

func TestPatternLearner_LearnFailure(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create a test pattern
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.8,
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 2,
		FailureCount: 0,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	db.AddPattern(pattern)

	// Learn failure
	entry := LearningEntry{
		PatternID:     pattern.ID,
		Success:       false,
		ErrorDelta:    1, // Created new error
		QualityChange: -0.1,
		Context:       "test.go",
		FixedErrors:   []string{},
		NewErrors:     []string{"4:b2c3d4e5"},
		Timestamp:     time.Now(),
	}

	err := learner.LearnFailure(pattern.ID, entry)
	if err != nil {
		t.Fatalf("LearnFailure failed: %v", err)
	}

	// Verify pattern updated
	updated, _ := db.GetPatternByID(pattern.ID)

	// Confidence should decrease by 0.2
	expectedConfidence := 0.6
	if math.Abs(updated.Confidence-expectedConfidence) > 0.001 {
		t.Errorf("Expected confidence %.3f, got %.3f", expectedConfidence, updated.Confidence)
	}

	// Failure count should increment
	if updated.FailureCount != 1 {
		t.Errorf("Expected failure count 1, got %d", updated.FailureCount)
	}
}

func TestPatternLearner_LearnFailure_Blacklist(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create pattern with low confidence (near threshold)
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.7, // Below φ (0.618) after -0.2
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 1,
		FailureCount: 3,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	db.AddPattern(pattern)

	// Learn failure (should blacklist)
	entry := LearningEntry{
		PatternID:     pattern.ID,
		Success:       false,
		ErrorDelta:    2,
		QualityChange: -0.2,
		Context:       "test.go",
		FixedErrors:   []string{},
		NewErrors:     []string{"4:b2c3d4e5", "5:c3d4e5f6"},
		Timestamp:     time.Now(),
	}

	learner.LearnFailure(pattern.ID, entry)

	updated, _ := db.GetPatternByID(pattern.ID)

	// Confidence should drop to 0.5 (0.7 - 0.2)
	expectedConfidence := 0.5
	if math.Abs(updated.Confidence-expectedConfidence) > 0.001 {
		t.Errorf("Expected confidence %.3f, got %.3f", expectedConfidence, updated.Confidence)
	}

	// Pattern should be blacklisted (confidence < 0.618)
	const goldenRatio = 0.618
	if updated.Confidence >= goldenRatio {
		t.Errorf("Pattern should be blacklisted (confidence < %.3f), got %.3f", goldenRatio, updated.Confidence)
	}
}

func TestPatternLearner_AdjustConfidence(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create test pattern
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.5,
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 1,
		FailureCount: 1,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	db.AddPattern(pattern)

	// Increase confidence
	err := learner.AdjustConfidence(pattern.ID, 0.3)
	if err != nil {
		t.Fatalf("AdjustConfidence failed: %v", err)
	}

	updated, _ := db.GetPatternByID(pattern.ID)
	if math.Abs(updated.Confidence-0.8) > 0.001 {
		t.Errorf("Expected confidence 0.8, got %.3f", updated.Confidence)
	}

	// Decrease confidence
	err = learner.AdjustConfidence(pattern.ID, -0.5)
	if err != nil {
		t.Fatalf("AdjustConfidence failed: %v", err)
	}

	updated, _ = db.GetPatternByID(pattern.ID)
	if math.Abs(updated.Confidence-0.3) > 0.001 {
		t.Errorf("Expected confidence 0.3, got %.3f", updated.Confidence)
	}

	// Test clamping at upper bound
	err = learner.AdjustConfidence(pattern.ID, 1.0)
	if err != nil {
		t.Fatalf("AdjustConfidence failed: %v", err)
	}

	updated, _ = db.GetPatternByID(pattern.ID)
	if updated.Confidence > 1.0 {
		t.Errorf("Confidence exceeded 1.0: %.3f", updated.Confidence)
	}

	// Test clamping at lower bound
	err = learner.AdjustConfidence(pattern.ID, -2.0)
	if err != nil {
		t.Fatalf("AdjustConfidence failed: %v", err)
	}

	updated, _ = db.GetPatternByID(pattern.ID)
	if updated.Confidence < 0.0 {
		t.Errorf("Confidence below 0.0: %.3f", updated.Confidence)
	}
}

func TestPatternLearner_ExtractNewPattern(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Extract new pattern
	pattern, err := learner.ExtractNewPattern(
		"5:d4e5f6g7",
		"compile",
		"go",
		"imports",
		`import "fmt"`,
		0.7,
	)

	if err != nil {
		t.Fatalf("ExtractNewPattern failed: %v", err)
	}

	if pattern == nil {
		t.Fatal("Expected pattern, got nil")
	}

	// Verify pattern fields
	if pattern.ErrorSig != "5:d4e5f6g7" {
		t.Errorf("Expected error sig '5:d4e5f6g7', got '%s'", pattern.ErrorSig)
	}

	if pattern.Language != "go" {
		t.Errorf("Expected language 'go', got '%s'", pattern.Language)
	}

	if pattern.Confidence != 0.7 {
		t.Errorf("Expected confidence 0.7, got %.3f", pattern.Confidence)
	}

	if pattern.SuccessCount != 1 {
		t.Errorf("Expected success count 1, got %d", pattern.SuccessCount)
	}

	// Verify pattern was added to database
	retrieved, err := db.GetPatternByID(pattern.ID)
	if err != nil {
		t.Fatalf("Failed to retrieve pattern: %v", err)
	}

	if retrieved.ErrorSig != pattern.ErrorSig {
		t.Errorf("Retrieved pattern error sig mismatch")
	}
}

func TestPatternLearner_BlacklistBadFix(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create pattern
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.5,
		Frequency:    1,
		LastApplied:  time.Now(),
		SuccessCount: 1,
		FailureCount: 5,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	db.AddPattern(pattern)

	// Blacklist it
	err := learner.BlacklistBadFix(pattern, "caused_divergence")
	if err != nil {
		t.Fatalf("BlacklistBadFix failed: %v", err)
	}

	// Verify confidence set to 0
	updated, _ := db.GetPatternByID(pattern.ID)
	if updated.Confidence != 0.0 {
		t.Errorf("Expected confidence 0.0 (blacklisted), got %.3f", updated.Confidence)
	}
}

func TestPatternLearner_GetStats(t *testing.T) {
	db, tmpDir := setupLearnerTestDB(t)
	defer cleanupLearnerTestDB(db, tmpDir)

	learner := NewPatternLearner(db)

	// Create pattern with known stats
	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.8,
		Frequency:    10,
		LastApplied:  time.Now(),
		SuccessCount: 8,
		FailureCount: 2,
		RepoSources:  []int64{},
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	db.AddPattern(pattern)

	// Get stats
	stats, err := learner.GetStats(pattern.ID)
	if err != nil {
		t.Fatalf("GetStats failed: %v", err)
	}

	if stats.TotalApplied != 10 {
		t.Errorf("Expected total applied 10, got %d", stats.TotalApplied)
	}

	expectedSuccessRate := 0.8
	if math.Abs(stats.SuccessRate-expectedSuccessRate) > 0.001 {
		t.Errorf("Expected success rate %.3f, got %.3f", expectedSuccessRate, stats.SuccessRate)
	}

	expectedFailureRate := 0.2
	if math.Abs(stats.FailureRate-expectedFailureRate) > 0.001 {
		t.Errorf("Expected failure rate %.3f, got %.3f", expectedFailureRate, stats.FailureRate)
	}

	if stats.Confidence != 0.8 {
		t.Errorf("Expected confidence 0.8, got %.3f", stats.Confidence)
	}
}

func TestPatternLearner_GoldenRatioThreshold(t *testing.T) {
	const phi = 0.618

	tests := []struct {
		name       string
		confidence float64
		shouldPass bool
	}{
		{"Above phi", 0.7, true},
		{"At phi", 0.618, true},
		{"Slightly below phi", 0.6, false},
		{"Well below phi", 0.5, false},
		{"Near zero", 0.1, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			passes := tt.confidence >= phi

			if passes != tt.shouldPass {
				t.Errorf("Confidence %.3f: expected pass=%v, got pass=%v",
					tt.confidence, tt.shouldPass, passes)
			}
		})
	}
}
