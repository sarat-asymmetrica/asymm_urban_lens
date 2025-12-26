// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Generator Tests
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"strings"
	"testing"
)

func TestPatternGenerator_GeneratePattern(t *testing.T) {
	diff := &CommitDiff{
		Files: []FileDiff{
			{
				Path:     "main.go",
				Language: "Go",
				Hunks: []DiffHunk{
					{
						OldStart:     10,
						OldLines:     3,
						NewStart:     10,
						NewLines:     4,
						RemovedLines: []string{"undefined: Foo"},
						AddedLines:   []string{"import \"foo\"", "Foo()"},
						Context:      []string{"package main", "func main() {"},
					},
				},
			},
		},
	}

	generator := NewPatternGenerator()
	pattern, err := generator.GeneratePattern(diff)

	if err != nil {
		t.Fatalf("GeneratePattern failed: %v", err)
	}

	if pattern.Language != "Go" {
		t.Errorf("Expected language Go, got %s", pattern.Language)
	}

	if pattern.ErrorType != "UNDEFINED_SYMBOL" {
		t.Errorf("Expected error type UNDEFINED_SYMBOL, got %s", pattern.ErrorType)
	}

	if pattern.SolutionCode == "" {
		t.Error("Solution code is empty")
	}

	if pattern.Confidence != 0.50 {
		t.Errorf("Expected confidence 0.50, got %.2f", pattern.Confidence)
	}

	if pattern.ErrorSig == "" {
		t.Error("Error signature is empty")
	}

	if !strings.Contains(pattern.ErrorSig, ":") {
		t.Errorf("Error signature should contain ':', got %s", pattern.ErrorSig)
	}

	t.Logf("Generated pattern: %s / %s / %s", pattern.ErrorType, pattern.Category, pattern.ErrorSig)
	t.Logf("Solution: %s", pattern.SolutionCode)
}

func TestPatternGenerator_ClassifyErrorType(t *testing.T) {
	generator := NewPatternGenerator()

	tests := []struct {
		removedLines []string
		context      []string
		expected     string
	}{
		{
			removedLines: []string{"undefined: Foo"},
			context:      []string{},
			expected:     "UNDEFINED_SYMBOL",
		},
		{
			removedLines: []string{"cannot use x (type int) as type string"},
			context:      []string{},
			expected:     "TYPE_MISMATCH",
		},
		{
			removedLines: []string{"imported and not used: \"fmt\""},
			context:      []string{},
			expected:     "UNUSED_IMPORT",
		},
		{
			removedLines: []string{"missing return at end of function"},
			context:      []string{},
			expected:     "MISSING_RETURN",
		},
		{
			removedLines: []string{"x.Foo has no method Bar"},
			context:      []string{},
			expected:     "MISSING_METHOD",
		},
		{
			removedLines: []string{"syntax error: unexpected }"},
			context:      []string{},
			expected:     "SYNTAX_ERROR",
		},
		{
			removedLines: []string{"some other error"},
			context:      []string{},
			expected:     "COMPILATION_ERROR",
		},
	}

	for _, test := range tests {
		hunk := DiffHunk{
			RemovedLines: test.removedLines,
			Context:      test.context,
		}

		result := generator.ClassifyErrorType(hunk)
		if result != test.expected {
			t.Errorf("ClassifyErrorType(%v) = %s, expected %s", test.removedLines, result, test.expected)
		}
	}
}

func TestPatternGenerator_GenerateErrorSignature(t *testing.T) {
	generator := NewPatternGenerator()

	sig1 := generator.GenerateErrorSignature("undefined: Foo")
	sig2 := generator.GenerateErrorSignature("undefined: Foo")
	sig3 := generator.GenerateErrorSignature("undefined: Bar")

	// Same input should produce same signature
	if sig1 != sig2 {
		t.Errorf("Same input produced different signatures: %s vs %s", sig1, sig2)
	}

	// Different input should produce different signatures
	if sig1 == sig3 {
		t.Errorf("Different inputs produced same signature: %s", sig1)
	}

	// Signature should have correct format (digit:hash)
	if !strings.Contains(sig1, ":") {
		t.Errorf("Signature missing ':' separator: %s", sig1)
	}

	parts := strings.Split(sig1, ":")
	if len(parts) != 2 {
		t.Errorf("Signature should have exactly 2 parts, got %d", len(parts))
	}

	// First part should be digit (1-9)
	if len(parts[0]) != 1 {
		t.Errorf("Digital root should be 1 digit, got %s", parts[0])
	}

	// Second part should be hash (8 chars)
	if len(parts[1]) != 8 {
		t.Errorf("Hash should be 8 chars, got %s (%d chars)", parts[1], len(parts[1]))
	}

	t.Logf("Signature examples: %s, %s", sig1, sig3)
}

func TestPatternGenerator_GenerateSolutionTemplate(t *testing.T) {
	generator := NewPatternGenerator()

	addedLines := []string{
		"import \"foo\"",
		"func Bar() {}",
	}

	template := generator.GenerateSolutionTemplate(addedLines)

	if template == "" {
		t.Error("Generated template is empty")
	}

	if !strings.Contains(template, "import") {
		t.Errorf("Template should contain 'import', got %s", template)
	}

	if !strings.Contains(template, "Bar") {
		t.Errorf("Template should contain 'Bar', got %s", template)
	}

	t.Logf("Generated template: %s", template)
}

func TestPatternGenerator_HashSolution(t *testing.T) {
	generator := NewPatternGenerator()

	hash1 := generator.HashSolution("import \"foo\"")
	hash2 := generator.HashSolution("import \"foo\"")
	hash3 := generator.HashSolution("import \"bar\"")

	// Same input should produce same hash
	if hash1 != hash2 {
		t.Errorf("Same input produced different hashes: %s vs %s", hash1, hash2)
	}

	// Different input should produce different hashes
	if hash1 == hash3 {
		t.Errorf("Different inputs produced same hash: %s", hash1)
	}

	// Hash should be 16 chars
	if len(hash1) != 16 {
		t.Errorf("Hash should be 16 chars, got %d", len(hash1))
	}

	t.Logf("Hash examples: %s, %s", hash1, hash3)
}

func TestIsKeyword(t *testing.T) {
	keywords := []string{"func", "package", "import", "var", "const", "if", "for"}
	nonKeywords := []string{"Foo", "bar", "myFunc", "customType"}

	for _, word := range keywords {
		if !isKeyword(word) {
			t.Errorf("isKeyword(%s) = false, expected true", word)
		}
	}

	for _, word := range nonKeywords {
		if isKeyword(word) {
			t.Errorf("isKeyword(%s) = true, expected false", word)
		}
	}
}

func TestIsBuiltinType(t *testing.T) {
	builtins := []string{"int", "string", "bool", "error", "float64", "byte", "rune"}
	nonBuiltins := []string{"Foo", "MyType", "CustomError", "User"}

	for _, typeName := range builtins {
		if !isBuiltinType(typeName) {
			t.Errorf("isBuiltinType(%s) = false, expected true", typeName)
		}
	}

	for _, typeName := range nonBuiltins {
		if isBuiltinType(typeName) {
			t.Errorf("isBuiltinType(%s) = true, expected false", typeName)
		}
	}
}

func TestPatternGenerator_EmptyDiff(t *testing.T) {
	diff := &CommitDiff{
		Files: []FileDiff{},
	}

	generator := NewPatternGenerator()
	_, err := generator.GeneratePattern(diff)

	if err == nil {
		t.Error("Expected error for empty diff, got nil")
	}

	if !strings.Contains(err.Error(), "no files") {
		t.Errorf("Expected error about 'no files', got %v", err)
	}
}

func TestPatternGenerator_NoHunks(t *testing.T) {
	diff := &CommitDiff{
		Files: []FileDiff{
			{
				Path:     "main.go",
				Language: "Go",
				Hunks:    []DiffHunk{},
			},
		},
	}

	generator := NewPatternGenerator()
	_, err := generator.GeneratePattern(diff)

	if err == nil {
		t.Error("Expected error for no hunks, got nil")
	}

	if !strings.Contains(err.Error(), "no hunks") {
		t.Errorf("Expected error about 'no hunks', got %v", err)
	}
}
