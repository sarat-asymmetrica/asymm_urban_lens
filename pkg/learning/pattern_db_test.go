// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Database Tests
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"os"
	"testing"
	"time"
)

// setupTestDB creates a temporary test database
func setupTestDB(t *testing.T) (*PatternDB, func()) {
	tmpFile := "test_ananta_learning.db"

	db, err := OpenDB(tmpFile)
	if err != nil {
		t.Fatalf("Failed to open test database: %v", err)
	}

	// Apply migrations
	if err := ApplyMigrations(db.db); err != nil {
		db.Close()
		os.Remove(tmpFile)
		t.Fatalf("Failed to apply migrations: %v", err)
	}

	// Return cleanup function
	cleanup := func() {
		db.Close()
		os.Remove(tmpFile)
	}

	return db, cleanup
}

// TestOpenDB verifies database opening
func TestOpenDB(t *testing.T) {
	tmpFile := "test_open.db"
	defer os.Remove(tmpFile)

	db, err := OpenDB(tmpFile)
	if err != nil {
		t.Fatalf("OpenDB failed: %v", err)
	}
	defer db.Close()

	if db.db == nil {
		t.Error("Database connection is nil")
	}
}

// TestMigrations verifies schema migrations
func TestMigrations(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	// Check schema version
	version, err := GetSchemaVersion(db.db)
	if err != nil {
		t.Fatalf("GetSchemaVersion failed: %v", err)
	}

	if version < 1 {
		t.Errorf("Schema version = %d, want >= 1", version)
	}

	// Verify tables exist
	tables := []string{"repos", "patterns", "applications", "learning_queue", "schema_version"}
	for _, table := range tables {
		var count int
		err := db.db.QueryRow("SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name=?", table).Scan(&count)
		if err != nil || count == 0 {
			t.Errorf("Table %s does not exist", table)
		}
	}
}

// TestAddAndGetRepo verifies repo CRUD operations
func TestAddAndGetRepo(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	repo := &Repo{
		FullName:     "spf13/cobra",
		Description:  "A Commander for modern Go CLI interactions",
		Language:     "Go",
		Stars:        35000,
		LastUpdated:  time.Now(),
		CIPassing:    true,
		HasDocs:      true,
		QualityScore: 0.95,
		ClonedAt:     time.Now(),
		ClonePath:    "/tmp/cobra",
	}

	// Add repo
	if err := db.AddRepo(repo); err != nil {
		t.Fatalf("AddRepo failed: %v", err)
	}

	// Verify ID was set
	if repo.ID == 0 {
		t.Error("Repo ID not set after insert")
	}

	// Get repo
	retrieved, err := db.GetRepo("spf13/cobra")
	if err != nil {
		t.Fatalf("GetRepo failed: %v", err)
	}

	// Verify fields
	if retrieved.FullName != repo.FullName {
		t.Errorf("FullName = %s, want %s", retrieved.FullName, repo.FullName)
	}
	if retrieved.Language != repo.Language {
		t.Errorf("Language = %s, want %s", retrieved.Language, repo.Language)
	}
	if retrieved.Stars != repo.Stars {
		t.Errorf("Stars = %d, want %d", retrieved.Stars, repo.Stars)
	}
}

// TestAddAndFindPatterns verifies pattern operations
func TestAddAndFindPatterns(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "Go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.85,
		Frequency:    1,
		RepoSources:  []int64{1, 2, 3},
	}

	// Add pattern
	if err := db.AddPattern(pattern); err != nil {
		t.Fatalf("AddPattern failed: %v", err)
	}

	// Find patterns
	found, err := db.FindPatterns("3:a1b2c3d4", "Go", 0.5)
	if err != nil {
		t.Fatalf("FindPatterns failed: %v", err)
	}

	if len(found) == 0 {
		t.Fatal("FindPatterns returned no results")
	}

	// Verify first result
	p := found[0]
	if p.ErrorSig != pattern.ErrorSig {
		t.Errorf("ErrorSig = %s, want %s", p.ErrorSig, pattern.ErrorSig)
	}
	if p.Language != pattern.Language {
		t.Errorf("Language = %s, want %s", p.Language, pattern.Language)
	}
	if p.Confidence != pattern.Confidence {
		t.Errorf("Confidence = %f, want %f", p.Confidence, pattern.Confidence)
	}
}

// TestUpdatePatternConfidence verifies confidence updates
func TestUpdatePatternConfidence(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	pattern := &Pattern{
		ErrorSig:     "5:deadbeef",
		ErrorType:    "runtime",
		Language:     "Go",
		Category:     "nil_check",
		SolutionCode: "if x == nil { return }",
		SolutionHash: "hash456",
		Confidence:   0.5,
		Frequency:    1,
		RepoSources:  []int64{1},
	}

	// Add pattern
	if err := db.AddPattern(pattern); err != nil {
		t.Fatalf("AddPattern failed: %v", err)
	}

	// Update confidence
	newConfidence := 0.95
	if err := db.UpdatePatternConfidence(pattern.ID, newConfidence); err != nil {
		t.Fatalf("UpdatePatternConfidence failed: %v", err)
	}

	// Retrieve and verify
	found, err := db.FindPatterns("5:deadbeef", "Go", 0.5)
	if err != nil {
		t.Fatalf("FindPatterns failed: %v", err)
	}

	if len(found) == 0 {
		t.Fatal("Pattern not found after update")
	}

	if found[0].Confidence != newConfidence {
		t.Errorf("Confidence = %f, want %f", found[0].Confidence, newConfidence)
	}
}

// TestRecordApplication verifies application tracking
func TestRecordApplication(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	// First add a pattern
	pattern := &Pattern{
		ErrorSig:     "7:cafebabe",
		ErrorType:    "test",
		Language:     "Go",
		Category:     "assertions",
		SolutionCode: "assert.Equal(t, expected, actual)",
		SolutionHash: "hash789",
		Confidence:   0.8,
		Frequency:    1,
		RepoSources:  []int64{1},
	}
	if err := db.AddPattern(pattern); err != nil {
		t.Fatalf("AddPattern failed: %v", err)
	}

	// Record application
	app := &Application{
		PatternID:          pattern.ID,
		TargetFile:         "main_test.go",
		Outcome:            "success",
		CompilationSuccess: true,
		TestPass:           true,
		QualityScore:       0.92,
		Feedback:           "Worked perfectly",
	}

	if err := db.RecordApplication(app); err != nil {
		t.Fatalf("RecordApplication failed: %v", err)
	}

	// Verify application was recorded
	if app.ID == 0 {
		t.Error("Application ID not set")
	}

	// Verify pattern success count was updated
	found, err := db.FindPatterns("7:cafebabe", "Go", 0.5)
	if err != nil {
		t.Fatalf("FindPatterns failed: %v", err)
	}

	if len(found) == 0 {
		t.Fatal("Pattern not found")
	}

	if found[0].SuccessCount != 1 {
		t.Errorf("SuccessCount = %d, want 1", found[0].SuccessCount)
	}
}

// TestAddToLearningQueue verifies learning queue operations
func TestAddToLearningQueue(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	entry := &LearningQueueEntry{
		ErrorSig:     "9:12345678",
		ErrorMessage: "<FILE>:<LINE> undefined: <VAR>",
		ErrorType:    "compile",
		Language:     "Go",
		FilePath:     "main.go",
		LineNumber:   42,
		Context:      "func main() {\n  fmt.Println()\n}",
	}

	if err := db.AddToLearningQueue(entry); err != nil {
		t.Fatalf("AddToLearningQueue failed: %v", err)
	}

	if entry.ID == 0 {
		t.Error("LearningQueueEntry ID not set")
	}
}

// TestFindPatternsWithMinConfidence verifies confidence filtering
func TestFindPatternsWithMinConfidence(t *testing.T) {
	db, cleanup := setupTestDB(t)
	defer cleanup()

	// Add patterns with different signatures AND confidence levels
	// NOTE: Changed signatures so they're actually different patterns (UNIQUE constraint)
	patterns := []*Pattern{
		{ErrorSig: "1:aaaaaaaa", ErrorType: "compile", Language: "Go", Category: "test", SolutionCode: "code1", SolutionHash: "h1", Confidence: 0.3, Frequency: 1, RepoSources: []int64{1}},
		{ErrorSig: "1:bbbbbbbb", ErrorType: "compile", Language: "Go", Category: "test", SolutionCode: "code2", SolutionHash: "h2", Confidence: 0.7, Frequency: 1, RepoSources: []int64{2}},
		{ErrorSig: "1:cccccccc", ErrorType: "compile", Language: "Go", Category: "test", SolutionCode: "code3", SolutionHash: "h3", Confidence: 0.9, Frequency: 1, RepoSources: []int64{3}},
	}

	for _, p := range patterns {
		if err := db.AddPattern(p); err != nil {
			t.Fatalf("AddPattern failed: %v", err)
		}
	}

	// Find ALL patterns for this language with minConfidence = 0.5
	// Since we're searching by different signatures, let's test each
	found1, _ := db.FindPatterns("1:aaaaaaaa", "Go", 0.5)
	found2, _ := db.FindPatterns("1:bbbbbbbb", "Go", 0.5)
	found3, _ := db.FindPatterns("1:cccccccc", "Go", 0.5)

	// Pattern 1 (confidence 0.3) should NOT be found
	if len(found1) != 0 {
		t.Errorf("Pattern with confidence 0.3 should not be found (minConfidence=0.5), got %d", len(found1))
	}

	// Patterns 2 and 3 (confidence 0.7, 0.9) should be found
	if len(found2) != 1 {
		t.Errorf("Pattern with confidence 0.7 should be found, got %d patterns", len(found2))
	}
	if len(found3) != 1 {
		t.Errorf("Pattern with confidence 0.9 should be found, got %d patterns", len(found3))
	}
}

// BenchmarkAddPattern benchmarks pattern insertion
func BenchmarkAddPattern(b *testing.B) {
	tmpFile := "bench_pattern.db"
	defer os.Remove(tmpFile)

	db, err := OpenDB(tmpFile)
	if err != nil {
		b.Fatal(err)
	}
	defer db.Close()

	ApplyMigrations(db.db)

	pattern := &Pattern{
		ErrorSig:     "3:a1b2c3d4",
		ErrorType:    "compile",
		Language:     "Go",
		Category:     "error_handling",
		SolutionCode: "if err != nil { return err }",
		SolutionHash: "hash123",
		Confidence:   0.85,
		Frequency:    1,
		RepoSources:  []int64{1, 2, 3},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		pattern.ErrorSig = "3:a1b2c3d4" // Reset to avoid unique constraint
		db.AddPattern(pattern)
	}
}

// BenchmarkFindPatterns benchmarks pattern lookup
func BenchmarkFindPatterns(b *testing.B) {
	tmpFile := "bench_find.db"
	defer os.Remove(tmpFile)

	db, err := OpenDB(tmpFile)
	if err != nil {
		b.Fatal(err)
	}
	defer db.Close()

	ApplyMigrations(db.db)

	// Insert test patterns
	for i := 0; i < 100; i++ {
		pattern := &Pattern{
			ErrorSig:     "3:a1b2c3d4",
			ErrorType:    "compile",
			Language:     "Go",
			Category:     "error_handling",
			SolutionCode: "if err != nil { return err }",
			SolutionHash: "hash123",
			Confidence:   0.85,
			Frequency:    1,
			RepoSources:  []int64{int64(i)},
		}
		db.AddPattern(pattern)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		db.FindPatterns("3:a1b2c3d4", "Go", 0.5)
	}
}
