// Package parsers implements language-specific AST parsing for pattern extraction
//
// Types: Common types used across all parsers
// Author: Agent 1.1 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package parsers

// PatternCategory represents classification of code patterns
type PatternCategory string

const (
	// ErrorHandling: Error checks, panic/recover, error wrapping
	ErrorHandling PatternCategory = "ERROR_HANDLING"

	// CRUDOperations: HTTP handlers, database queries, REST operations
	CRUDOperations PatternCategory = "CRUD_OPS"

	// Testing: Test functions, assertions, test fixtures
	Testing PatternCategory = "TESTING"

	// Imports: Common library imports, dependency patterns
	Imports PatternCategory = "IMPORTS"

	// NullSafety: Null checks, optional chaining, safe navigation
	NullSafety PatternCategory = "NULL_SAFETY"

	// Async: Goroutines, channels, async/await patterns
	Async PatternCategory = "ASYNC"

	// TypeGuards: Type assertions, interface checks, type safety
	TypeGuards PatternCategory = "TYPE_GUARDS"

	// Logging: Structured logging, log levels, context propagation
	Logging PatternCategory = "LOGGING"
)

// ExtractedPattern represents a code pattern extracted from source
type ExtractedPattern struct {
	Category    PatternCategory // ERROR_HANDLING, CRUD_OPS, etc.
	Language    string          // Go, TypeScript, Python, Rust
	FilePath    string          // Source file path
	StartLine   int             // Starting line number
	EndLine     int             // Ending line number
	Code        string          // Actual code snippet
	Description string          // Human-readable description
	Keywords    []string        // Keywords that identify this pattern
}

// LanguageParser interface for all language parsers
type LanguageParser interface {
	// ExtractPatterns extracts all patterns from a source file
	ExtractPatterns(filePath string) ([]*ExtractedPattern, error)
}
