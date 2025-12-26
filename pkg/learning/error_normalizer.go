// Package learning implements Ananta's self-healing pattern database and error classification
//
// Error Normalizer: Remove file-specific details to enable pattern matching
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"regexp"
	"strings"
)

// Regex patterns for normalization
var (
	// File paths: Matches file paths and simple filenames
	// /path/to/file.go → <FILE>, C:\path\to\file.go → <FILE>, main.go → <FILE>
	filePathPattern = regexp.MustCompile(`[/\\]?(?:[A-Za-z]:[/\\])?(?:[\w.-]+[/\\])+[\w.-]+\.\w+|[\w.-]+\.go`)

	// Line numbers: :42 or :123: → :<LINE>
	lineNumberPattern = regexp.MustCompile(`:(\d+):?`)

	// Variable names in error messages (heuristic: identifiers after certain keywords)
	// Examples: "undefined: myVar" → "undefined: <VAR>"
	// Captures both lowercase and mixed case identifiers
	variablePattern = regexp.MustCompile(`(undefined|undeclared|not defined|unknown identifier):\s+([a-zA-Z_][a-zA-Z0-9_]*)`)

	// "cannot use" pattern (separate because it has different structure)
	cannotUsePattern = regexp.MustCompile(`cannot use\s+([a-zA-Z_][a-zA-Z0-9_]*)`)

	// Type names (heuristic: capitalized identifiers in type contexts)
	// Examples: "type MyType is not" → "type <TYPE> is not"
	typePattern = regexp.MustCompile(`(type|struct|interface)\s+([A-Z][a-zA-Z0-9_]*)`)

	// Package names: github.com/user/repo/pkg → <PKG>
	packagePattern = regexp.MustCompile(`(?:github\.com|golang\.org|gopkg\.in)[/\\][\w.-]+[/\\][\w.-]+(?:[/\\][\w.-]+)*`)

	// Memory addresses: 0xc0000b4000 → <ADDR>
	memoryAddrPattern = regexp.MustCompile(`0x[0-9a-fA-F]+`)

	// String literals: "some string" → <STR>
	stringLiteralPattern = regexp.MustCompile(`"[^"]*"`)

	// Numeric literals (standalone numbers that aren't part of identifiers)
	numericLiteralPattern = regexp.MustCompile(`\b\d+\b`)
)

// NormalizeError removes file-specific details from error message
// to create a canonical form suitable for pattern matching.
//
// Normalization steps:
//  1. Replace file paths with <FILE>
//  2. Replace line numbers with <LINE>
//  3. Replace variable names with <VAR>
//  4. Replace type names with <TYPE>
//  5. Replace package names with <PKG>
//  6. Replace memory addresses with <ADDR>
//  7. Optionally: string literals, numeric literals
//
// Example:
//
//	Input:  "main.go:42: undefined: fmt"
//	Output: "<FILE>:<LINE> undefined: <VAR>"
//
// This ensures:
//
//	"main.go:42: undefined: fmt" and
//	"handler.go:123: undefined: fmt"
//
// normalize to the SAME string, producing the SAME signature.
func NormalizeError(errorMsg string) string {
	// Step 1: Remove file paths
	normalized := filePathPattern.ReplaceAllString(errorMsg, "<FILE>")

	// Step 2: Remove line numbers
	normalized = lineNumberPattern.ReplaceAllString(normalized, ":<LINE>")

	// Step 3: Remove package paths
	normalized = packagePattern.ReplaceAllString(normalized, "<PKG>")

	// Step 4: Remove memory addresses
	normalized = memoryAddrPattern.ReplaceAllString(normalized, "<ADDR>")

	// Step 5: Normalize variable names (context-aware)
	normalized = variablePattern.ReplaceAllString(normalized, "$1: <VAR>")
	normalized = cannotUsePattern.ReplaceAllString(normalized, "cannot use <VAR>")

	// Step 6: Normalize type names (context-aware)
	normalized = typePattern.ReplaceAllString(normalized, "$1 <TYPE>")

	// Step 7: Collapse multiple whitespace
	normalized = strings.Join(strings.Fields(normalized), " ")

	return normalized
}

// RemoveFilePaths replaces all file paths with <FILE>
func RemoveFilePaths(s string) string {
	return filePathPattern.ReplaceAllString(s, "<FILE>")
}

// RemoveLineNumbers replaces all line numbers with <LINE>
func RemoveLineNumbers(s string) string {
	return lineNumberPattern.ReplaceAllString(s, ":<LINE>")
}

// RemoveVariableNames removes lowercase identifiers after specific keywords
//
// This is a HEURISTIC. It catches common patterns like:
// - "undefined: myVar"
// - "undeclared: someFunc"
// - "cannot use varName"
//
// But may miss context-specific variable references.
func RemoveVariableNames(s string) string {
	return variablePattern.ReplaceAllString(s, "$1: <VAR>")
}

// RemoveTypeNames removes capitalized identifiers in type contexts
//
// This is a HEURISTIC. It catches:
// - "type MyStruct is not"
// - "struct MyType has no field"
//
// But may miss some type references depending on error format.
func RemoveTypeNames(s string) string {
	return typePattern.ReplaceAllString(s, "$1 <TYPE>")
}

// RemovePackagePaths replaces Go package import paths with <PKG>
func RemovePackagePaths(s string) string {
	return packagePattern.ReplaceAllString(s, "<PKG>")
}

// RemoveMemoryAddresses replaces hex memory addresses with <ADDR>
func RemoveMemoryAddresses(s string) string {
	return memoryAddrPattern.ReplaceAllString(s, "<ADDR>")
}

// RemoveStringLiterals replaces "quoted strings" with <STR>
// WARNING: Use carefully - may remove important error context
func RemoveStringLiterals(s string) string {
	return stringLiteralPattern.ReplaceAllString(s, "<STR>")
}

// RemoveNumericLiterals replaces standalone numbers with <NUM>
// WARNING: Use carefully - may remove important error context (like line numbers already handled)
func RemoveNumericLiterals(s string) string {
	return numericLiteralPattern.ReplaceAllString(s, "<NUM>")
}

// AggressiveNormalization applies ALL normalization steps, including
// string and numeric literals. Use when you want maximum generalization.
//
// WARNING: This may be TOO aggressive, removing meaningful error context.
// Use NormalizeError() for standard normalization.
func AggressiveNormalization(errorMsg string) string {
	normalized := NormalizeError(errorMsg)
	normalized = RemoveStringLiterals(normalized)
	normalized = RemoveNumericLiterals(normalized)
	return strings.Join(strings.Fields(normalized), " ")
}
