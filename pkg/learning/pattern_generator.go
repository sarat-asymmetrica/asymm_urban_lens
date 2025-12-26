// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Generator: Converts commit diffs into reusable patterns
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"crypto/sha256"
	"fmt"
	"regexp"
	"strings"
)

// PatternGenerator converts commit fixes into patterns
type PatternGenerator struct{}

// NewPatternGenerator creates a new pattern generator
func NewPatternGenerator() *PatternGenerator {
	return &PatternGenerator{}
}

// GeneratePattern creates a pattern from a commit diff
//
// Process:
//  1. Identify error type from removed lines
//  2. Extract fix from added lines
//  3. Generate error signature (Vedic digital root)
//  4. Classify error category
//  5. Calculate initial confidence (0.50 for new patterns)
//  6. Create Pattern object
func (pg *PatternGenerator) GeneratePattern(diff *CommitDiff) (*Pattern, error) {
	if len(diff.Files) == 0 {
		return nil, fmt.Errorf("no files in diff")
	}

	// Process first file (focus on primary change)
	file := diff.Files[0]
	if len(file.Hunks) == 0 {
		return nil, fmt.Errorf("no hunks in file")
	}

	hunk := file.Hunks[0]

	// Identify error type
	errorType := pg.ClassifyErrorType(hunk)

	// Extract error context and fix
	parser := &DiffParser{}
	errorContext := parser.ExtractErrorContext(hunk)
	fix := parser.ExtractFix(hunk)

	if fix == "" {
		return nil, fmt.Errorf("no fix found in diff")
	}

	// Generate error signature using Vedic digital root
	errorSig := pg.GenerateErrorSignature(errorContext)

	// Classify category (using normalized error text)
	normalizedError := NormalizeError(errorContext)
	category := ClassifyError(normalizedError)

	// Generate solution template with placeholders
	solutionTemplate := pg.GenerateSolutionTemplate(hunk.AddedLines)

	// Hash solution for grouping
	solutionHash := pg.HashSolution(solutionTemplate)

	return &Pattern{
		ErrorSig:     errorSig,
		ErrorType:    errorType,
		Language:     file.Language,
		Category:     category,
		SolutionCode: solutionTemplate,
		SolutionHash: solutionHash,
		Confidence:   0.50, // Initial confidence for new patterns
		Frequency:    0,
		RepoSources:  []int64{},
	}, nil
}

// ClassifyErrorType determines error type from diff hunk
//
// Looks for patterns in removed lines:
// - "undefined: X" → UNDEFINED_SYMBOL
// - "cannot use X (type Y) as type Z" → TYPE_MISMATCH
// - "imported and not used" → UNUSED_IMPORT
// - "missing return" → MISSING_RETURN
// - "has no method" → MISSING_METHOD
func (pg *PatternGenerator) ClassifyErrorType(hunk DiffHunk) string {
	// Combine removed lines and context
	allText := strings.Join(hunk.RemovedLines, " ") + " " + strings.Join(hunk.Context, " ")
	allText = strings.ToLower(allText)

	// Pattern matching
	if strings.Contains(allText, "undefined:") || strings.Contains(allText, "not defined") {
		return "UNDEFINED_SYMBOL"
	}
	if strings.Contains(allText, "type mismatch") || strings.Contains(allText, "cannot use") {
		return "TYPE_MISMATCH"
	}
	if strings.Contains(allText, "imported and not used") || strings.Contains(allText, "unused import") {
		return "UNUSED_IMPORT"
	}
	if strings.Contains(allText, "missing return") {
		return "MISSING_RETURN"
	}
	if strings.Contains(allText, "has no method") || strings.Contains(allText, "does not implement") {
		return "MISSING_METHOD"
	}
	if strings.Contains(allText, "syntax error") {
		return "SYNTAX_ERROR"
	}
	if strings.Contains(allText, "undeclared name") {
		return "UNDECLARED_NAME"
	}

	return "COMPILATION_ERROR"
}

// GenerateErrorSignature creates a digital root signature for error
//
// Format: "DR:hash" where DR is digital root (1-9) and hash is first 8 chars
func (pg *PatternGenerator) GenerateErrorSignature(errorText string) string {
	// Normalize error text
	normalized := strings.ToLower(strings.TrimSpace(errorText))

	// Calculate hash
	hash := sha256.Sum256([]byte(normalized))
	hashStr := fmt.Sprintf("%x", hash)[:8]

	// Calculate digital root using Vedic mathematics (use local DigitalRoot from error_classifier.go)
	dr := DigitalRoot(uint64(hash[0]))

	return fmt.Sprintf("%d:%s", dr, hashStr)
}

// ExtractPlaceholders identifies variables/types to parameterize
//
// Replaces specific identifiers with placeholders:
// - Variable names → <VAR>
// - Type names → <TYPE>
// - Package names → <PKG>
// - Function names → <FUNC>
func (pg *PatternGenerator) ExtractPlaceholders(code string) map[string]string {
	placeholders := make(map[string]string)

	// Pattern for Go variable names
	varPattern := regexp.MustCompile(`\b[a-z][a-zA-Z0-9]*\b`)
	// Pattern for Go type names (capitalized)
	typePattern := regexp.MustCompile(`\b[A-Z][a-zA-Z0-9]*\b`)
	// Pattern for package names (unused for now, but kept for future use)
	_ = regexp.MustCompile(`\b[a-z][a-z0-9]*\.[A-Z]`)

	// Extract variables
	vars := varPattern.FindAllString(code, -1)
	for _, v := range vars {
		if !isKeyword(v) {
			placeholders[v] = "<VAR>"
		}
	}

	// Extract types
	types := typePattern.FindAllString(code, -1)
	for _, t := range types {
		if !isBuiltinType(t) {
			placeholders[t] = "<TYPE>"
		}
	}

	return placeholders
}

// GenerateSolutionTemplate creates reusable solution with placeholders
//
// Converts specific code into template by replacing identifiers with placeholders.
func (pg *PatternGenerator) GenerateSolutionTemplate(addedLines []string) string {
	code := strings.Join(addedLines, "\n")

	// For now, return as-is (future: smart placeholder replacement)
	// This keeps specific context which is valuable for early patterns
	return strings.TrimSpace(code)
}

// HashSolution creates hash for solution grouping
func (pg *PatternGenerator) HashSolution(solution string) string {
	hash := sha256.Sum256([]byte(solution))
	return fmt.Sprintf("%x", hash)[:16]
}

// isKeyword checks if identifier is a Go keyword
func isKeyword(word string) bool {
	keywords := map[string]bool{
		"break": true, "case": true, "chan": true, "const": true, "continue": true,
		"default": true, "defer": true, "else": true, "fallthrough": true, "for": true,
		"func": true, "go": true, "goto": true, "if": true, "import": true,
		"interface": true, "map": true, "package": true, "range": true, "return": true,
		"select": true, "struct": true, "switch": true, "type": true, "var": true,
	}
	return keywords[word]
}

// isBuiltinType checks if type is a Go builtin
func isBuiltinType(typeName string) bool {
	builtins := map[string]bool{
		"bool": true, "byte": true, "complex64": true, "complex128": true,
		"error": true, "float32": true, "float64": true,
		"int": true, "int8": true, "int16": true, "int32": true, "int64": true,
		"rune": true, "string": true,
		"uint": true, "uint8": true, "uint16": true, "uint32": true, "uint64": true, "uintptr": true,
	}
	return builtins[typeName]
}
