// Demo test showing complete Agent 0.3 workflow
package learning

import (
	"fmt"
	"os"
	"testing"
)

func TestAgent03_CompleteDemo(t *testing.T) {
	// Step 1: Open database
	dbPath := "demo_ananta_learning.db"
	defer os.Remove(dbPath)

	db, err := OpenDB(dbPath)
	if err != nil {
		t.Fatalf("OpenDB failed: %v", err)
	}
	defer db.Close()

	// Step 2: Apply migrations
	if err := ApplyMigrations(db.db); err != nil {
		t.Fatalf("Migrations failed: %v", err)
	}

	fmt.Println("✓ Database created with schema")

	// Step 3: Classify errors
	err1 := "main.go:42: undefined: fmt"
	err2 := "handler.go:123: undefined: fmt"
	err3 := "server.go:999: syntax error: unexpected }"

	class1 := ClassifyFullError(err1)
	class2 := ClassifyFullError(err2)
	class3 := ClassifyFullError(err3)

	fmt.Printf("✓ Error 1 classified: %s (type: %s, DR: %d)\n", class1.Signature, class1.ErrorType, class1.DigitalRoot)
	fmt.Printf("✓ Error 2 classified: %s (type: %s, DR: %d)\n", class2.Signature, class2.ErrorType, class2.DigitalRoot)
	fmt.Printf("✓ Error 3 classified: %s (type: %s, DR: %d)\n", class3.Signature, class3.ErrorType, class3.DigitalRoot)

	// Verify same error → same signature
	if class1.Signature != class2.Signature {
		t.Errorf("Same error should have same signature: %s != %s", class1.Signature, class2.Signature)
	}

	// Verify different error → different signature
	if class1.Signature == class3.Signature {
		t.Error("Different errors should have different signatures")
	}

	fmt.Println("✓ Same error different files → SAME signature (VERIFIED)")

	// Step 4: Add pattern to database
	pattern := &Pattern{
		ErrorSig:     class1.Signature,
		ErrorType:    class1.ErrorType,
		Language:     "Go",
		Category:     "imports",
		SolutionCode: `import "fmt"`,
		SolutionHash: "fmt_import_fix",
		Confidence:   0.95,
		Frequency:    1,
		RepoSources:  []int64{1},
	}

	if err := db.AddPattern(pattern); err != nil {
		t.Fatalf("AddPattern failed: %v", err)
	}

	fmt.Printf("✓ Pattern added to database (ID: %d)\n", pattern.ID)

	// Step 5: Find pattern
	found, err := db.FindPatterns(class1.Signature, "Go", 0.5)
	if err != nil {
		t.Fatalf("FindPatterns failed: %v", err)
	}

	if len(found) == 0 {
		t.Fatal("Pattern not found")
	}

	fmt.Printf("✓ Pattern found: %s (confidence: %.2f)\n", found[0].SolutionCode, found[0].Confidence)

	// Step 6: Record successful application
	app := &Application{
		PatternID:          pattern.ID,
		TargetFile:         "main.go",
		Outcome:            "success",
		CompilationSuccess: true,
		TestPass:           true,
		QualityScore:       0.92,
	}

	if err := db.RecordApplication(app); err != nil {
		t.Fatalf("RecordApplication failed: %v", err)
	}

	fmt.Printf("✓ Application recorded (outcome: %s)\n", app.Outcome)

	// Step 7: Verify pattern success count updated
	updated, _ := db.FindPatterns(class1.Signature, "Go", 0.5)
	if updated[0].SuccessCount != 1 {
		t.Errorf("Success count = %d, want 1", updated[0].SuccessCount)
	}

	fmt.Println("✓ Pattern success count incremented")
	fmt.Println("\n=== AGENT 0.3 COMPLETE DEMO: ALL SYSTEMS OPERATIONAL ===")
}
