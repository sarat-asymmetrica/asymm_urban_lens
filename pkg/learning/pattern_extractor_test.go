// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Extractor Tests
// Author: Agent 1.1 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"os"
	"path/filepath"
	"testing"
)

func TestWilliamsBatchSize(t *testing.T) {
	tests := []struct {
		name     string
		n        int
		expected int
	}{
		{"Zero files", 0, 1},
		{"One file", 1, 1},
		{"Ten files", 10, 9},     // sqrt(10)=3, log2(10)=3, 3*3=9
		{"Hundred files", 100, 60},  // sqrt(100)=10, log2(100)=6, 10*6=60
		{"Thousand files", 1000, 279}, // sqrt(1000)=31, log2(1000)=9, 31*9=279
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := WilliamsBatchSize(tt.n)
			// Allow small variation due to integer math
			if result < tt.expected-10 || result > tt.expected+10 {
				t.Errorf("WilliamsBatchSize(%d) = %d, want approximately %d", tt.n, result, tt.expected)
			}
		})
	}
}

func TestLanguageExtensions(t *testing.T) {
	tests := []struct {
		language string
		expected []string
	}{
		{"Go", []string{".go"}},
		{"TypeScript", []string{".ts", ".tsx"}},
		{"JavaScript", []string{".js", ".jsx"}},
		{"Python", []string{".py"}},
		{"Rust", []string{".rs"}},
		{"Unknown", nil},
	}

	for _, tt := range tests {
		t.Run(tt.language, func(t *testing.T) {
			result := LanguageExtensions(tt.language)
			if len(result) != len(tt.expected) {
				t.Errorf("LanguageExtensions(%s) returned %d extensions, want %d",
					tt.language, len(result), len(tt.expected))
				return
			}

			for i, ext := range tt.expected {
				if i >= len(result) || result[i] != ext {
					t.Errorf("LanguageExtensions(%s)[%d] = %s, want %s",
						tt.language, i, result[i], ext)
				}
			}
		})
	}
}

func TestNormalizeCodePattern(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected string
	}{
		{
			name:     "Trim whitespace",
			input:    "  if err != nil {\n    return err\n  }  ",
			expected: "if err != nil {\n    return err\n  }",
		},
		{
			name:     "Normalize tabs",
			input:    "if err != nil {\n\treturn err\n}",
			expected: "if err != nil {\n  return err\n}",
		},
		{
			name:     "Empty string",
			input:    "",
			expected: "",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := NormalizeCodePattern(tt.input)
			if result != tt.expected {
				t.Errorf("NormalizeCodePattern() = %q, want %q", result, tt.expected)
			}
		})
	}
}

func TestFindSourceFiles(t *testing.T) {
	// Create temporary test directory
	tmpDir, err := os.MkdirTemp("", "pattern_extractor_test")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create test files
	testFiles := []string{
		"main.go",
		"handler.go",
		"main_test.go",       // Should be skipped
		"vendor/dep.go",      // Should be skipped
		".hidden/secret.go",  // Should be skipped
		"sub/utils.go",
		"sub/utils_test.go",  // Should be skipped
	}

	for _, file := range testFiles {
		fullPath := filepath.Join(tmpDir, file)
		dir := filepath.Dir(fullPath)
		if err := os.MkdirAll(dir, 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(fullPath, []byte("package main"), 0644); err != nil {
			t.Fatal(err)
		}
	}

	// Test finding Go files
	extractor := NewPatternExtractor(nil)
	files, err := extractor.FindSourceFiles(tmpDir, "Go")
	if err != nil {
		t.Fatalf("FindSourceFiles() error = %v", err)
	}

	// Should find: main.go, handler.go, sub/utils.go (3 files, excluding tests and vendor)
	expectedCount := 3
	if len(files) != expectedCount {
		t.Errorf("FindSourceFiles() found %d files, want %d", len(files), expectedCount)
	}

	// Verify test files are excluded
	for _, file := range files {
		if filepath.Base(file) == "main_test.go" {
			t.Error("FindSourceFiles() should exclude test files")
		}
		if filepath.Dir(file) == filepath.Join(tmpDir, "vendor") {
			t.Error("FindSourceFiles() should exclude vendor directory")
		}
	}
}

func TestExtractFromFile_Go(t *testing.T) {
	// Create temporary test file with Go code
	tmpDir, err := os.MkdirTemp("", "go_parser_test")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	testFile := filepath.Join(tmpDir, "test.go")
	testCode := `package main

import "fmt"

func DoSomething() error {
	if err := someFunc(); err != nil {
		return fmt.Errorf("failed: %w", err)
	}
	return nil
}
`
	if err := os.WriteFile(testFile, []byte(testCode), 0644); err != nil {
		t.Fatal(err)
	}

	// Extract patterns
	extractor := NewPatternExtractor(nil)
	patterns, err := extractor.ExtractFromFile(testFile, "Go")
	if err != nil {
		t.Fatalf("ExtractFromFile() error = %v", err)
	}

	// Should find at least one error handling pattern
	if len(patterns) == 0 {
		t.Error("ExtractFromFile() found no patterns, expected at least 1 error handling pattern")
	}

	// Verify pattern has required fields
	for _, p := range patterns {
		if p.Language != "Go" {
			t.Errorf("Pattern language = %s, want Go", p.Language)
		}
		if p.SolutionCode == "" {
			t.Error("Pattern has empty SolutionCode")
		}
		if p.SolutionHash == "" {
			t.Error("Pattern has empty SolutionHash")
		}
		if p.ErrorSig == "" {
			t.Error("Pattern has empty ErrorSig")
		}
	}
}

func TestReadCodeSnippet(t *testing.T) {
	// Create temporary test file
	tmpDir, err := os.MkdirTemp("", "code_snippet_test")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	testFile := filepath.Join(tmpDir, "test.go")
	testContent := `line 1
line 2
line 3
line 4
line 5`
	if err := os.WriteFile(testFile, []byte(testContent), 0644); err != nil {
		t.Fatal(err)
	}

	extractor := NewPatternExtractor(nil)

	tests := []struct {
		name      string
		startLine int
		endLine   int
		expected  string
		wantErr   bool
	}{
		{
			name:      "Single line",
			startLine: 2,
			endLine:   2,
			expected:  "line 2",
			wantErr:   false,
		},
		{
			name:      "Multiple lines",
			startLine: 2,
			endLine:   4,
			expected:  "line 2\nline 3\nline 4",
			wantErr:   false,
		},
		{
			name:      "All lines",
			startLine: 1,
			endLine:   5,
			expected:  "line 1\nline 2\nline 3\nline 4\nline 5",
			wantErr:   false,
		},
		{
			name:      "Invalid start line",
			startLine: 0,
			endLine:   2,
			expected:  "",
			wantErr:   true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, err := extractor.readCodeSnippet(testFile, tt.startLine, tt.endLine)
			if (err != nil) != tt.wantErr {
				t.Errorf("readCodeSnippet() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !tt.wantErr && result != tt.expected {
				t.Errorf("readCodeSnippet() = %q, want %q", result, tt.expected)
			}
		})
	}
}

func BenchmarkWilliamsBatchSize(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = WilliamsBatchSize(1000)
	}
}

func BenchmarkNormalizeCodePattern(b *testing.B) {
	code := `if err != nil {
		return fmt.Errorf("failed: %w", err)
	}`
	for i := 0; i < b.N; i++ {
		_ = NormalizeCodePattern(code)
	}
}
