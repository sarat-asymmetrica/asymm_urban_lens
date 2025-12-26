package healing

import "time"

// Fix represents a surgical code fix ready for application
type Fix struct {
	ID              string    // Unique fix ID (UUID)
	ErrorID         string    // Reference to error (file:line format)
	PatternID       int64     // Reference to pattern that generated this fix
	MatchScore      float64   // Combined confidence × similarity score
	FixType         FixType   // Type of fix operation
	TargetFile      string    // File to modify
	TargetLine      int       // Line number to modify (1-indexed)
	TargetColumn    int       // Column position (optional, 0 if not applicable)
	OriginalCode    string    // Current code at target location
	ReplacementCode string    // New code to insert/replace
	Indentation     int       // Number of spaces/tabs for indentation
	ImportsToAdd    []string  // Import statements to add
	Confidence      float64   // Overall confidence in this fix (0.0-1.0)
	Rationale       string    // Human-readable explanation of why this fix
	CreatedAt       time.Time // When fix was generated
}

// FixType represents the kind of surgical operation to perform
type FixType string

const (
	// ADD_LINE inserts a new line at the target location
	ADD_LINE FixType = "ADD_LINE"

	// REPLACE_LINE replaces the existing line with new code
	REPLACE_LINE FixType = "REPLACE_LINE"

	// ADD_IMPORT adds an import statement to the file
	ADD_IMPORT FixType = "ADD_IMPORT"

	// REMOVE_LINE deletes the target line
	REMOVE_LINE FixType = "REMOVE_LINE"

	// MODIFY_BLOCK changes an entire block of code (multi-line)
	MODIFY_BLOCK FixType = "MODIFY_BLOCK"

	// WRAP_WITH wraps the target line with a construct (e.g., if err != nil)
	WRAP_WITH FixType = "WRAP_WITH"
)

// CompilationError represents an error detected by Agent 2.1
// This is the input to fix generation
type CompilationError struct {
	FilePath       string
	LineNumber     int
	Column         int
	ErrorMessage   string
	ErrorType      string // compile, runtime, test, lint
	ErrorSignature string // Vedic digital root signature
	Context        ErrorContext
}

// ErrorContext provides surrounding code context for fix adaptation
type ErrorContext struct {
	SurroundingLines []string // Lines before and after error
	FunctionName     string   // Name of containing function
	FunctionDepth    int      // Nesting level (0 = package level)
	Imports          []string // Import statements in the file
	PackageName      string   // Package name
	Dependencies     []string // Packages used in error context
}

// PatternMatch represents a matched pattern from Agent 2.2
// This is the other input to fix generation
type PatternMatch struct {
	Pattern        Pattern // The matched pattern
	CombinedScore  float64 // Combined confidence × similarity
	Confidence     float64 // Pattern confidence from learning
	Similarity     float64 // Semantic similarity to error
	MatchRationale string  // Why this pattern matched
}

// Pattern represents a learned error-solution pattern
// This mirrors the learning.Pattern type but is healing-specific
type Pattern struct {
	ID            int64
	ErrorClass    string // ERROR_HANDLING, LOGGING, etc.
	ErrorSignature string // Vedic digital root signature
	ProblemCode   string // Example code that has the error
	SolutionCode  string // Example code that fixes it (with placeholders)
	Explanation   string // Why this fixes the error
	Confidence    float64 // Learned confidence score
}
