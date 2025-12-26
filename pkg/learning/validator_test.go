// Package learning implements Ananta's self-healing pattern database and error classification
//
// Tests for Pattern Validator
// Author: Agent 6.2 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"os"
	"path/filepath"
	"testing"
)

func TestQuickValidate(t *testing.T) {
	testDir := filepath.Join(os.TempDir(), "ananta_validator_test")
	validator, err := NewPatternValidator(testDir)
	if err != nil {
		t.Fatalf("Failed to create validator: %v", err)
	}
	defer validator.Cleanup()

	tests := []struct {
		name     string
		pattern  *Pattern
		wantValid bool
	}{
		{
			name: "valid_go_statement",
			pattern: &Pattern{
				Language:     "Go",
				SolutionCode: "if err != nil { return err }",
			},
			wantValid: true,
		},
		{
			name: "valid_go_expression",
			pattern: &Pattern{
				Language:     "Go",
				SolutionCode: "fmt.Errorf(\"error: %w\", err)",
			},
			wantValid: true,
		},
		{
			name: "empty_solution",
			pattern: &Pattern{
				Language:     "Go",
				SolutionCode: "",
			},
			wantValid: false,
		},
		{
			name: "whitespace_only",
			pattern: &Pattern{
				Language:     "Go",
				SolutionCode: "   \n\t   ",
			},
			wantValid: false,
		},
		{
			name: "comments_only",
			pattern: &Pattern{
				Language:     "Go",
				SolutionCode: "// Just a comment",
			},
			wantValid: false,
		},
		{
			name: "invalid_syntax",
			pattern: &Pattern{
				Language:     "Go",
				SolutionCode: "if err { { { return",
			},
			wantValid: false,
		},
		{
			name: "non_go_language",
			pattern: &Pattern{
				Language:     "Python",
				SolutionCode: "if err: return err",
			},
			wantValid: false, // Not supported yet
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			valid := validator.QuickValidate(tt.pattern)

			if valid != tt.wantValid {
				t.Errorf("QuickValidate() = %v, want %v", valid, tt.wantValid)
			}
		})
	}
}

func TestValidatorCleanup(t *testing.T) {
	testDir := filepath.Join(os.TempDir(), "ananta_validator_cleanup_test")

	validator, err := NewPatternValidator(testDir)
	if err != nil {
		t.Fatalf("Failed to create validator: %v", err)
	}

	// Verify directory was created
	if _, err := os.Stat(testDir); os.IsNotExist(err) {
		t.Error("Test directory was not created")
	}

	// Cleanup
	if err := validator.Cleanup(); err != nil {
		t.Errorf("Cleanup failed: %v", err)
	}

	// Verify directory was removed
	if _, err := os.Stat(testDir); !os.IsNotExist(err) {
		t.Error("Test directory was not removed after cleanup")
	}
}

func TestNewPatternValidator_CreatesDirectory(t *testing.T) {
	testDir := filepath.Join(os.TempDir(), "ananta_validator_new_dir_test")

	// Ensure directory doesn't exist
	os.RemoveAll(testDir)

	validator, err := NewPatternValidator(testDir)
	if err != nil {
		t.Fatalf("Failed to create validator: %v", err)
	}
	defer validator.Cleanup()

	// Verify directory was created
	if _, err := os.Stat(testDir); os.IsNotExist(err) {
		t.Error("Validator did not create test directory")
	}
}
