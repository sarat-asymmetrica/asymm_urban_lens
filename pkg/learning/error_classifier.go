// Package learning implements Ananta's self-healing pattern database and error classification
//
// Error Classifier: Compute deterministic signatures using Vedic mathematics
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"strings"
)

// DigitalRoot computes the digital root of a number using Vedic mathematics
// Formula: ((n - 1) % 9) + 1, with special case for 0
//
// The digital root reduces any number to 1-9 for O(1) classification.
// Examples:
//   - 12345 → 1+2+3+4+5 = 15 → 1+5 = 6
//   - 99 → 9+9 = 18 → 1+8 = 9
//   - 0 → 0 (special case)
//
// This function is IDENTICAL to backend/pkg/ocr/vedic.go:DigitalRoot
// but operates on uint64 instead of int for hash compatibility.
func DigitalRoot(n uint64) uint8 {
	if n == 0 {
		return 0
	}
	root := n % 9
	if root == 0 {
		return 9
	}
	return uint8(root)
}

// ClassifyError computes a deterministic signature from normalized error
//
// Algorithm:
//  1. Compute SHA256 hash of normalized error
//  2. Convert first 8 bytes to uint64
//  3. Apply digital root: dr = DigitalRoot(hashUint64)
//  4. Format signature: "{dr}:{first_8_hex_chars}"
//
// Example:
//
//	Input:  "<FILE>:<LINE> undefined: <VAR>"
//	Hash:   a1b2c3d4e5f67890... (32 bytes)
//	Uint64: 0xa1b2c3d4e5f67890
//	DR:     DigitalRoot(0xa1b2c3d4e5f67890) = 3
//	Output: "3:a1b2c3d4"
//
// Properties:
//   - DETERMINISTIC: Same input → same output (always)
//   - O(1) CLASSIFICATION: Digital root bucketing (1-9)
//   - COLLISION RESISTANT: SHA256 provides strong uniqueness
//   - COMPACT: "3:a1b2c3d4" (10 bytes) vs full hash (64 bytes)
//
// This enables:
//   - Fast lookup: Index by (signature, language)
//   - Digital root bucketing: 9 categories for pattern clustering
//   - Database efficiency: Small index keys
func ClassifyError(normalizedError string) string {
	// Step 1: Compute SHA256 hash
	hash := sha256.Sum256([]byte(normalizedError))

	// Step 2: Convert first 8 bytes to uint64 (big endian)
	hashUint64 := binary.BigEndian.Uint64(hash[:8])

	// Step 3: Compute digital root
	dr := DigitalRoot(hashUint64)

	// Step 4: Format signature: "{dr}:{first_8_hex_chars}"
	hexPrefix := hex.EncodeToString(hash[:4]) // First 4 bytes = 8 hex chars
	signature := fmt.Sprintf("%d:%s", dr, hexPrefix)

	return signature
}

// DetermineErrorType classifies error message into type categories
//
// Categories:
//   - "compile": Compilation errors (syntax, type errors, undefined symbols)
//   - "runtime": Runtime errors (panics, nil pointers, index out of range)
//   - "test": Test failures (assertions, test framework errors)
//   - "lint": Linter warnings (style, conventions, recommendations)
//
// Detection heuristics (keyword-based):
//   - Compile: "cannot", "undefined", "undeclared", "syntax error", "type mismatch"
//   - Runtime: "panic", "nil pointer", "index out of range", "runtime error"
//   - Test: "FAIL:", "test failed", "assertion", "expected"
//   - Lint: "should", "recommended", "consider", "ineffective", "unused"
//
// Returns "unknown" if no pattern matches.
func DetermineErrorType(errorMsg string) string {
	lower := strings.ToLower(errorMsg)

	// Check for test errors FIRST (most specific keywords)
	testKeywords := []string{
		"fail:",
		"test failed",
		"assertion",
		"got:",
		"want:",
		"testing.t",
		"assertion failed",
		"expected true",
		"expected false",
	}
	for _, keyword := range testKeywords {
		if strings.Contains(lower, keyword) {
			return "test"
		}
	}

	// Check for runtime errors
	runtimeKeywords := []string{
		"panic",
		"nil pointer",
		"index out of range",
		"runtime error",
		"slice bounds",
		"division by zero",
		"deadlock",
		"goroutine",
		"fatal error",
		"concurrent map",
	}
	for _, keyword := range runtimeKeywords {
		if strings.Contains(lower, keyword) {
			return "runtime"
		}
	}

	// Check for compile errors
	compileKeywords := []string{
		"cannot",
		"undefined",
		"undeclared",
		"syntax error",
		"type mismatch",
		"missing",
		"not defined",
		"does not exist",
		"has no field",
		"has no method",
		"invalid operation",
	}
	for _, keyword := range compileKeywords {
		if strings.Contains(lower, keyword) {
			return "compile"
		}
	}

	// Check for lint warnings
	lintKeywords := []string{
		"should",
		"recommended",
		"consider",
		"ineffective",
		"unused",
		"exported",
		"comment",
		"golint",
		"staticcheck",
	}
	for _, keyword := range lintKeywords {
		if strings.Contains(lower, keyword) {
			return "lint"
		}
	}

	// Unknown type (rare case - maybe custom error format)
	return "unknown"
}

// ErrorClassification combines all error classification data
type ErrorClassification struct {
	NormalizedError string // Normalized form (file/line/var replaced)
	Signature       string // Digital root signature "3:a1b2c3d4"
	ErrorType       string // compile, runtime, test, lint, unknown
	DigitalRoot     uint8  // Digital root value (1-9, 0 for zero hash)
}

// ClassifyFullError performs complete error classification in one call
//
// This is the main entry point for error classification.
// It combines normalization, signature computation, and type detection.
//
// Example:
//
//	input := "main.go:42: undefined: fmt"
//	result := ClassifyFullError(input)
//	// result.NormalizedError = "<FILE>:<LINE> undefined: <VAR>"
//	// result.Signature = "3:a1b2c3d4" (example)
//	// result.ErrorType = "compile"
//	// result.DigitalRoot = 3
func ClassifyFullError(errorMsg string) ErrorClassification {
	// Step 1: Normalize error
	normalized := NormalizeError(errorMsg)

	// Step 2: Compute signature
	signature := ClassifyError(normalized)

	// Step 3: Determine error type
	errorType := DetermineErrorType(errorMsg) // Use original message for better detection

	// Step 4: Extract digital root from signature (first character before ':')
	var dr uint8
	if len(signature) > 0 {
		// Parse "3:a1b2c3d4" → dr = 3
		fmt.Sscanf(signature, "%d:", &dr)
	}

	return ErrorClassification{
		NormalizedError: normalized,
		Signature:       signature,
		ErrorType:       errorType,
		DigitalRoot:     dr,
	}
}

// ComputeSignatureDirect computes signature from already-normalized error
// Use this if you've already normalized the error and just need the signature.
func ComputeSignatureDirect(normalizedError string) string {
	return ClassifyError(normalizedError)
}

// CompareErrors checks if two error messages are equivalent (same signature)
//
// Returns true if both errors normalize to the same signature,
// meaning they represent the same underlying error pattern.
func CompareErrors(err1, err2 string) bool {
	norm1 := NormalizeError(err1)
	norm2 := NormalizeError(err2)
	sig1 := ClassifyError(norm1)
	sig2 := ClassifyError(norm2)
	return sig1 == sig2
}
