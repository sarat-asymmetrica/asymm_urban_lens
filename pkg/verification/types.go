// Package verification implements compilation verification and regression detection
//
// Verification Types: Core data structures for verification results
// Author: Agent 4.1 (Dr. Liam O'Connor - Formal Verification, Oxford)
// Created: 2025-11-07
// Ported: 2025-12-26 (Urban Lens Integration)
//
// This package verifies that applied fixes actually improve compilation state
// by running the compiler, parsing results, and detecting regressions.
package verification

import (
	"time"

	"github.com/asymmetrica/urbanlens/pkg/reasoning"
)

// VerificationResult captures outcome of fix verification
type VerificationResult struct {
	Success             bool                 // Overall success (errors decreased, no critical regressions)
	ErrorsBefore        int                  // Error count before fix
	ErrorsAfter         int                  // Error count after fix
	ErrorsFixed         int                  // Number of errors resolved
	NewErrorsIntroduced int                  // Number of new errors introduced
	Regressions         []Regression         // New errors introduced by fix
	CompilationTime     time.Duration        // Time taken to compile
	CompilerOutput      string               // Raw compiler output
	Timestamp           time.Time            // When verification ran
	ErrorDiff           *ErrorDiff           // Detailed diff of errors
	AcceptableTradeoff  bool                 // Whether regression is acceptable
	QualityScore        float64              // Harmonic mean quality score (0.0-1.0)
}

// Regression represents a new error introduced by fix
type Regression struct {
	FilePath     string             // File where regression occurred
	LineNumber   int                // Line number (1-indexed)
	ErrorMessage string             // Full error message
	ErrorType    string             // Type of error (compile, runtime, etc)
	Severity     RegressionSeverity // How bad is this regression
}

// RegressionSeverity classifies how bad a regression is
type RegressionSeverity string

const (
	// SeverityCritical - Syntax error, undefined symbol (show-stopper)
	SeverityCritical RegressionSeverity = "critical"

	// SeverityMajor - Type mismatch, missing import (significant issue)
	SeverityMajor RegressionSeverity = "major"

	// SeverityMinor - Warning, unused variable (cosmetic issue)
	SeverityMinor RegressionSeverity = "minor"
)

// ErrorDiff shows what changed between before/after compilation
type ErrorDiff struct {
	Fixed          []reasoning.CompilationError // Errors that disappeared
	New            []reasoning.CompilationError // New errors introduced
	Unchanged      []reasoning.CompilationError // Errors still present
	FixedCount     int                          // Count of fixed errors
	NewCount       int                          // Count of new errors
	UnchangedCount int                          // Count of unchanged errors
}

// BuildOutput captures compiler execution results
type BuildOutput struct {
	ExitCode int           // Compiler exit code (0 = success)
	Stdout   string        // Standard output
	Stderr   string        // Standard error
	Duration time.Duration // Time taken to run
	Success  bool          // Whether compilation succeeded
}
