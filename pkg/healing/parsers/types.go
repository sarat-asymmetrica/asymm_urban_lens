// Package parsers implements language-specific error parsing
package parsers

// CompilationError represents a basic compilation error (before context extraction)
// This is a lightweight version used by parsers - the full CompilationError with
// context is in the parent healing package.
type CompilationError struct {
	FilePath     string // Absolute path to file
	LineNumber   int    // Line where error occurred (1-indexed)
	Column       int    // Column position (1-indexed)
	ErrorMessage string // Full error message from compiler
}
