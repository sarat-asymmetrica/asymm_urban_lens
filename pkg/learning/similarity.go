// Package learning implements Ananta's self-healing pattern database and error classification
//
// Similarity: Structural similarity algorithms for pattern grouping
// Author: Agent 1.2 (Dr. Sofia Hernandez - Statistician)
// Created: 2025-11-07
package learning

import (
	"crypto/sha256"
	"fmt"
	"regexp"
	"strings"
	"unicode"
)

// AreSimilar checks if two patterns are structurally similar
//
// Returns:
//   - bool: true if similarity >= 0.85 (85% threshold)
//   - float64: similarity score [0.0, 1.0]
//
// Algorithm:
//  1. Fast path: Check solution_hash for exact duplicates (O(1))
//  2. Slow path: Normalize code → compute Levenshtein on AST structure (O(n²))
//  3. Threshold: 85% similarity for grouping
func AreSimilar(p1, p2 *Pattern) (bool, float64) {
	// PHASE 1: Exact duplicate detection (fast path)
	if p1.SolutionHash == p2.SolutionHash && p1.SolutionHash != "" {
		return true, 1.0
	}

	// PHASE 2: Structural similarity (slower, more flexible)
	norm1 := NormalizeSolution(p1.SolutionCode)
	norm2 := NormalizeSolution(p2.SolutionCode)

	// Empty normalized solutions are not similar
	if norm1 == "" || norm2 == "" {
		return false, 0.0
	}

	similarity := StructuralSimilarity(norm1, norm2)

	// Threshold: 85% structural match
	return similarity >= 0.85, similarity
}

// NormalizeSolution normalizes code for structural comparison
//
// Transformations:
//  1. Remove comments (// ... and /* ... */)
//  2. Normalize whitespace (collapse multiple spaces/newlines)
//  3. Replace identifiers WHILE preserving literals inline
//  4. Keep: keywords, operators, structure
//
// Example:
//
//	Input:  if err != nil { return fmt.Errorf("error: %v", err) }
//	Output: if <VAR> != nil { return <FUNC>(<LITERAL>, <VAR>) }
func NormalizeSolution(code string) string {
	// Step 1: Remove comments
	code = removeComments(code)

	// Step 2: Normalize whitespace
	code = normalizeWhitespace(code)

	// Step 3: Replace identifiers AND literals together
	// (to avoid double-processing)
	code = replaceIdentifiersAndLiterals(code)

	// Step 4: Final cleanup
	code = strings.TrimSpace(code)

	return code
}

// removeComments strips // and /* */ comments
func removeComments(code string) string {
	// Remove single-line comments (// ...)
	singleLineRe := regexp.MustCompile(`//[^\n]*`)
	code = singleLineRe.ReplaceAllString(code, "")

	// Remove multi-line comments (/* ... */)
	multiLineRe := regexp.MustCompile(`/\*[\s\S]*?\*/`)
	code = multiLineRe.ReplaceAllString(code, "")

	return code
}

// normalizeWhitespace collapses whitespace sequences
func normalizeWhitespace(code string) string {
	// Replace tabs with spaces
	code = strings.ReplaceAll(code, "\t", " ")

	// Collapse multiple spaces
	spaceRe := regexp.MustCompile(`  +`)
	code = spaceRe.ReplaceAllString(code, " ")

	// Collapse multiple newlines
	newlineRe := regexp.MustCompile(`\n\n+`)
	code = newlineRe.ReplaceAllString(code, "\n")

	return code
}

// replaceIdentifiersAndLiterals replaces both identifiers and literals in one pass
// This avoids the double-processing issue where <LITERAL> becomes <TYPE>
func replaceIdentifiersAndLiterals(code string) string {
	// Common keywords across languages (Go, TypeScript, Python, Rust)
	keywords := map[string]bool{
		// Control flow
		"if": true, "else": true, "elif": true, "switch": true, "case": true, "default": true,
		"for": true, "while": true, "do": true, "break": true, "continue": true,
		"return": true, "yield": true, "await": true, "async": true,
		// Error handling
		"try": true, "catch": true, "finally": true, "throw": true, "raise": true, "panic": true, "recover": true,
		// Types
		"int": true, "float": true, "bool": true, "string": true, "var": true, "let": true, "const": true,
		"type": true, "interface": true, "struct": true, "class": true, "enum": true,
		// Scope
		"func": true, "fn": true, "def": true, "function": true,
		"import": true, "from": true, "package": true, "use": true, "crate": true,
		"pub": true, "private": true, "public": true, "protected": true, "static": true,
		// Memory
		"new": true, "make": true, "delete": true, "free": true,
		// Comparison
		"nil": true, "null": true, "undefined": true, "None": true, "true": true, "false": true, "True": true, "False": true,
		// Other
		"in": true, "not": true, "and": true, "or": true, "is": true,
		"defer": true, "go": true, "chan": true, "select": true, "map": true, "range": true,
	}

	// Split code into tokens
	var result strings.Builder
	i := 0
	for i < len(code) {
		ch := rune(code[i])

		// Handle string literals
		if ch == '"' || ch == '\'' {
			quote := code[i]
			i++
			// Skip to closing quote
			for i < len(code) && code[i] != quote {
				if code[i] == '\\' && i+1 < len(code) {
					i += 2 // Skip escaped character
				} else {
					i++
				}
			}
			if i < len(code) {
				i++ // Skip closing quote
			}
			result.WriteString("<LITERAL>")
			continue
		}

		// Handle numeric literals
		if unicode.IsDigit(ch) {
			for i < len(code) && (unicode.IsDigit(rune(code[i])) || code[i] == '.') {
				i++
			}
			// Check for scientific notation (e+10, E-5)
			if i < len(code) && (code[i] == 'e' || code[i] == 'E') {
				i++
				if i < len(code) && (code[i] == '+' || code[i] == '-') {
					i++
				}
				for i < len(code) && unicode.IsDigit(rune(code[i])) {
					i++
				}
			}
			result.WriteString("<LITERAL>")
			continue
		}

		// Preserve operators and punctuation
		if !unicode.IsLetter(ch) && ch != '_' {
			result.WriteByte(code[i])
			i++
			continue
		}

		// Extract identifier
		identStart := i
		for i < len(code) && (unicode.IsLetter(rune(code[i])) || unicode.IsDigit(rune(code[i])) || code[i] == '_') {
			i++
		}
		identifier := code[identStart:i]

		// Keep keywords, replace identifiers
		if keywords[strings.ToLower(identifier)] {
			result.WriteString(identifier)
		} else {
			// Classify identifier type
			if isCapitalized(identifier) {
				result.WriteString("<TYPE>")
			} else if isFunctionCall(code, i) {
				result.WriteString("<FUNC>")
			} else {
				result.WriteString("<VAR>")
			}
		}
	}

	return result.String()
}

// isCapitalized checks if identifier starts with uppercase (likely a type)
func isCapitalized(s string) bool {
	if len(s) == 0 {
		return false
	}
	return unicode.IsUpper(rune(s[0]))
}

// isFunctionCall checks if identifier is followed by '(' (function call)
func isFunctionCall(code string, pos int) bool {
	// Skip whitespace after identifier
	for pos < len(code) && unicode.IsSpace(rune(code[pos])) {
		pos++
	}
	return pos < len(code) && code[pos] == '('
}

// StructuralSimilarity computes similarity score using Levenshtein distance
//
// Returns similarity ∈ [0.0, 1.0]:
//   - 1.0 = identical
//   - 0.85 = threshold for grouping
//   - 0.0 = completely different
func StructuralSimilarity(s1, s2 string) float64 {
	// Edge cases
	if s1 == s2 {
		return 1.0
	}
	if len(s1) == 0 || len(s2) == 0 {
		return 0.0
	}

	// Compute Levenshtein distance
	distance := levenshteinDistance(s1, s2)

	// Normalize to [0, 1] similarity
	maxLen := max(len(s1), len(s2))
	similarity := 1.0 - float64(distance)/float64(maxLen)

	return similarity
}

// levenshteinDistance computes edit distance between two strings
//
// Algorithm: Dynamic programming (Wagner-Fischer)
// Time complexity: O(m × n)
// Space complexity: O(min(m, n)) with optimization
func levenshteinDistance(s1, s2 string) int {
	// Ensure s1 is shorter for space optimization
	if len(s1) > len(s2) {
		s1, s2 = s2, s1
	}

	// Create DP array (only need current and previous row)
	prev := make([]int, len(s1)+1)
	curr := make([]int, len(s1)+1)

	// Initialize first row
	for i := range prev {
		prev[i] = i
	}

	// Fill DP table
	for j := 1; j <= len(s2); j++ {
		curr[0] = j

		for i := 1; i <= len(s1); i++ {
			if s1[i-1] == s2[j-1] {
				curr[i] = prev[i-1] // Match
			} else {
				// Min of: insert, delete, replace
				curr[i] = 1 + min3(curr[i-1], prev[i], prev[i-1])
			}
		}

		// Swap rows
		prev, curr = curr, prev
	}

	return prev[len(s1)]
}

// min3 returns minimum of three integers
func min3(a, b, c int) int {
	if a < b {
		if a < c {
			return a
		}
		return c
	}
	if b < c {
		return b
	}
	return c
}

// max returns maximum of two integers
func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

// GroupByHash groups patterns by solution hash (exact duplicates)
//
// Returns map: hash → list of patterns
func GroupByHash(patterns []*Pattern) map[string][]*Pattern {
	groups := make(map[string][]*Pattern)

	for _, p := range patterns {
		hash := p.SolutionHash
		if hash == "" {
			// Generate hash if missing
			hash = HashSolution(p.SolutionCode)
			p.SolutionHash = hash
		}

		groups[hash] = append(groups[hash], p)
	}

	return groups
}

// HashSolution generates SHA-256 hash of normalized solution code
func HashSolution(code string) string {
	normalized := NormalizeSolution(code)
	hash := sha256.Sum256([]byte(normalized))
	return fmt.Sprintf("%x", hash[:8]) // First 8 bytes (16 hex chars)
}
