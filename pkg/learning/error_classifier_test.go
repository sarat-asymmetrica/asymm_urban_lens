// Package learning implements Ananta's self-healing pattern database and error classification
//
// Error Classifier Tests
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"testing"
)

// TestDigitalRoot verifies the Vedic digital root computation
func TestDigitalRoot(t *testing.T) {
	tests := []struct {
		input    uint64
		expected uint8
	}{
		{0, 0},       // Special case: zero
		{1, 1},       // Base case
		{9, 9},       // Single digit
		{10, 1},      // 1+0 = 1
		{99, 9},      // 9+9 = 18 → 1+8 = 9
		{12345, 6},   // 1+2+3+4+5 = 15 → 1+5 = 6
		{999999, 9},  // All 9s
		{100, 1},     // 1+0+0 = 1
		{54, 9},      // 5+4 = 9
		{123456789, 9}, // Large number
	}

	for _, tt := range tests {
		result := DigitalRoot(tt.input)
		if result != tt.expected {
			t.Errorf("DigitalRoot(%d) = %d, want %d", tt.input, result, tt.expected)
		}
	}
}

// TestClassifyError verifies deterministic signature computation
func TestClassifyError(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{"simple error", "<FILE>:<LINE> undefined: <VAR>"},
		{"complex error", "<FILE>:<LINE> cannot use <VAR> (type <TYPE>) as type <TYPE>"},
		{"runtime error", "panic: runtime error: index out of range [<NUM>] with length <NUM>"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			sig1 := ClassifyError(tt.input)
			sig2 := ClassifyError(tt.input)

			// Deterministic: same input → same signature
			if sig1 != sig2 {
				t.Errorf("ClassifyError not deterministic: got %s and %s", sig1, sig2)
			}

			// Format check: should be "{dr}:{hex}"
			if len(sig1) < 3 || sig1[1] != ':' {
				t.Errorf("ClassifyError invalid format: %s", sig1)
			}

			// Digital root should be 1-9 or 0
			dr := sig1[0]
			if dr < '0' || dr > '9' {
				t.Errorf("ClassifyError invalid digital root: %c", dr)
			}
		})
	}
}

// TestDetermineErrorType verifies error type classification
func TestDetermineErrorType(t *testing.T) {
	tests := []struct {
		errorMsg     string
		expectedType string
	}{
		// Compile errors
		{"undefined: fmt", "compile"},
		{"cannot use x (type int) as type string", "compile"},
		{"syntax error: unexpected }", "compile"},
		{"type MyStruct has no field Name", "compile"},
		{"missing return at end of function", "compile"},

		// Runtime errors
		{"panic: runtime error: index out of range", "runtime"},
		{"panic: nil pointer dereference", "runtime"},
		{"fatal error: concurrent map writes", "runtime"},
		{"goroutine 1 [running]:", "runtime"},

		// Test errors
		{"FAIL: TestMyFunction", "test"},
		{"test failed: got 42, want 21", "test"},
		{"assertion failed: expected true", "test"},

		// Lint warnings
		{"should have comment", "lint"},
		{"exported function should have doc comment", "lint"},
		{"unused variable x", "lint"},
		{"ineffective assignment", "lint"},

		// Unknown
		{"some random error", "unknown"},
	}

	for _, tt := range tests {
		t.Run(tt.errorMsg, func(t *testing.T) {
			result := DetermineErrorType(tt.errorMsg)
			if result != tt.expectedType {
				t.Errorf("DetermineErrorType(%q) = %s, want %s", tt.errorMsg, result, tt.expectedType)
			}
		})
	}
}

// TestClassifyFullError verifies complete error classification
func TestClassifyFullError(t *testing.T) {
	errorMsg := "main.go:42: undefined: fmt"

	result := ClassifyFullError(errorMsg)

	// Check normalized error
	if result.NormalizedError != "<FILE>:<LINE> undefined: <VAR>" {
		t.Errorf("NormalizedError = %q, want %q", result.NormalizedError, "<FILE>:<LINE> undefined: <VAR>")
	}

	// Check signature is non-empty and has correct format
	if len(result.Signature) < 3 || result.Signature[1] != ':' {
		t.Errorf("Signature has invalid format: %s", result.Signature)
	}

	// Check error type
	if result.ErrorType != "compile" {
		t.Errorf("ErrorType = %s, want compile", result.ErrorType)
	}

	// Check digital root is valid (1-9 or 0)
	if result.DigitalRoot < 0 || result.DigitalRoot > 9 {
		t.Errorf("DigitalRoot = %d, want 0-9", result.DigitalRoot)
	}
}

// TestSameErrorDifferentFiles verifies that identical errors in different files
// produce the SAME signature (critical for pattern matching)
func TestSameErrorDifferentFiles(t *testing.T) {
	err1 := "main.go:42: undefined: fmt"
	err2 := "handler.go:123: undefined: fmt"
	err3 := "/Users/dev/project/api/server.go:999: undefined: fmt"

	sig1 := ClassifyError(NormalizeError(err1))
	sig2 := ClassifyError(NormalizeError(err2))
	sig3 := ClassifyError(NormalizeError(err3))

	if sig1 != sig2 {
		t.Errorf("Same error different files should have same signature:\n  err1 sig: %s\n  err2 sig: %s", sig1, sig2)
	}

	if sig1 != sig3 {
		t.Errorf("Same error different paths should have same signature:\n  err1 sig: %s\n  err3 sig: %s", sig1, sig3)
	}
}

// TestDifferentErrorsDifferentSignatures verifies that different errors
// produce DIFFERENT signatures
func TestDifferentErrorsDifferentSignatures(t *testing.T) {
	err1 := "main.go:42: undefined: fmt"
	err2 := "main.go:42: syntax error: unexpected }"

	sig1 := ClassifyError(NormalizeError(err1))
	sig2 := ClassifyError(NormalizeError(err2))

	if sig1 == sig2 {
		t.Errorf("Different errors should have different signatures:\n  err1: %s\n  err2: %s\n  both got: %s", err1, err2, sig1)
	}
}

// TestCompareErrors verifies the error comparison utility
func TestCompareErrors(t *testing.T) {
	// Same error, different files → should be equivalent
	if !CompareErrors("main.go:42: undefined: fmt", "handler.go:123: undefined: fmt") {
		t.Error("Same error different files should be equivalent")
	}

	// Different errors → should NOT be equivalent
	if CompareErrors("undefined: fmt", "syntax error") {
		t.Error("Different errors should not be equivalent")
	}
}

// TestComputeSignatureDirect verifies direct signature computation
func TestComputeSignatureDirect(t *testing.T) {
	normalized := "<FILE>:<LINE> undefined: <VAR>"

	sig1 := ComputeSignatureDirect(normalized)
	sig2 := ComputeSignatureDirect(normalized)

	// Deterministic
	if sig1 != sig2 {
		t.Errorf("ComputeSignatureDirect not deterministic: %s != %s", sig1, sig2)
	}

	// Should be same as ClassifyError
	sig3 := ClassifyError(normalized)
	if sig1 != sig3 {
		t.Errorf("ComputeSignatureDirect != ClassifyError: %s != %s", sig1, sig3)
	}
}

// BenchmarkDigitalRoot benchmarks the digital root computation
func BenchmarkDigitalRoot(b *testing.B) {
	for i := 0; i < b.N; i++ {
		DigitalRoot(uint64(i))
	}
}

// BenchmarkClassifyError benchmarks signature computation
func BenchmarkClassifyError(b *testing.B) {
	normalized := "<FILE>:<LINE> undefined: <VAR>"
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		ClassifyError(normalized)
	}
}

// BenchmarkDetermineErrorType benchmarks error type classification
func BenchmarkDetermineErrorType(b *testing.B) {
	errorMsg := "main.go:42: undefined: fmt"
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		DetermineErrorType(errorMsg)
	}
}

// BenchmarkClassifyFullError benchmarks complete error classification
func BenchmarkClassifyFullError(b *testing.B) {
	errorMsg := "main.go:42: undefined: fmt"
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		ClassifyFullError(errorMsg)
	}
}
