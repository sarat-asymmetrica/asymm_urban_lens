// Package learning implements Ananta's self-healing pattern database and error classification
//
// Validator: Pattern validation through syntax and compilation checks
// Author: Agent 6.2 (Dr. Yuki Tanaka - Data Quality & ML Specialist)
// Created: 2025-11-07
package learning

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

// PatternValidator tests if patterns are syntactically and semantically valid
type PatternValidator struct {
	testDir string // Temporary directory for validation tests
}

// NewPatternValidator creates a pattern validator
//
// testDir: Directory for temporary test files (will be created if missing)
func NewPatternValidator(testDir string) (*PatternValidator, error) {
	// Create test directory if it doesn't exist
	if err := os.MkdirAll(testDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create test directory: %w", err)
	}

	return &PatternValidator{
		testDir: testDir,
	}, nil
}

// ValidationResult captures pattern validation outcome
type ValidationResult struct {
	Valid          bool          // Overall validity
	CompilesBefore bool          // Did error code compile (should be false)
	CompilesAfter  bool          // Did fixed code compile (should be true)
	ErrorMessage   string        // Error message if validation failed
	Duration       time.Duration // Time taken for validation
}

// ValidatePattern performs full validation (expensive - use sparingly)
//
// Process:
//  1. Create minimal test file with the error
//  2. Verify it fails to compile (error reproduction)
//  3. Apply pattern's solution
//  4. Verify it compiles successfully (fix works)
//  5. Clean up test files
//
// Note: This is EXPENSIVE (spawns compiler). Only use for high-value patterns.
// For bulk validation, use QuickValidate instead.
func (pv *PatternValidator) ValidatePattern(pattern *Pattern) (*ValidationResult, error) {
	start := time.Now()

	result := &ValidationResult{}

	// Only support Go for now (can extend to other languages)
	if pattern.Language != "Go" {
		result.ErrorMessage = fmt.Sprintf("validation not supported for language: %s", pattern.Language)
		return result, nil
	}

	// Create test file with error
	testFile := filepath.Join(pv.testDir, fmt.Sprintf("pattern_%d_test.go", time.Now().UnixNano()))
	defer os.Remove(testFile) // Clean up

	// Generate test code with error
	errorCode := generateTestCodeWithError(pattern)
	if err := os.WriteFile(testFile, []byte(errorCode), 0644); err != nil {
		return nil, fmt.Errorf("failed to write test file: %w", err)
	}

	// PHASE 1: Verify error code fails to compile
	compilesBefore, _ := pv.tryCompile(testFile)
	result.CompilesBefore = compilesBefore

	// If error code compiles, this isn't a real error pattern
	if compilesBefore {
		result.ErrorMessage = "error code compiles (not a real error pattern)"
		result.Duration = time.Since(start)
		return result, nil
	}

	// PHASE 2: Apply solution and verify it compiles
	fixedCode := applyPatternSolution(errorCode, pattern)
	if err := os.WriteFile(testFile, []byte(fixedCode), 0644); err != nil {
		return nil, fmt.Errorf("failed to write fixed file: %w", err)
	}

	compilesAfter, errMsg := pv.tryCompile(testFile)
	result.CompilesAfter = compilesAfter

	if !compilesAfter {
		result.ErrorMessage = fmt.Sprintf("fixed code doesn't compile: %s", errMsg)
		result.Duration = time.Since(start)
		return result, nil
	}

	// SUCCESS: Error code failed, fixed code compiled
	result.Valid = true
	result.Duration = time.Since(start)

	return result, nil
}

// QuickValidate performs fast syntax-only validation
//
// Checks:
//  1. Solution is valid Go syntax (can be parsed)
//  2. Has required structure (not empty, not just whitespace)
//  3. Contains actual code (not just comments)
//
// This is O(n) where n = code length, much faster than full compilation.
// Use this for bulk validation.
func (pv *PatternValidator) QuickValidate(pattern *Pattern) bool {
	// Only support Go for now
	if pattern.Language != "Go" {
		return false
	}

	solution := pattern.SolutionCode

	// Check 1: Not empty
	if strings.TrimSpace(solution) == "" {
		return false
	}

	// Check 2: Valid Go syntax
	fset := token.NewFileSet()

	// Try parsing as expression first
	_, err := parser.ParseExpr(solution)
	if err == nil {
		return true // Valid expression
	}

	// Try parsing as statement(s)
	// Wrap in function for parsing
	wrapped := fmt.Sprintf("package main\nfunc test() {\n%s\n}", solution)
	_, err = parser.ParseFile(fset, "test.go", wrapped, parser.AllErrors)

	if err != nil {
		// Not valid syntax
		return false
	}

	// Check 3: Contains actual code (not just comments/whitespace)
	// Parse AST and check for statements
	file, _ := parser.ParseFile(fset, "test.go", wrapped, parser.ParseComments)
	if file == nil {
		return false
	}

	hasCode := false
	ast.Inspect(file, func(n ast.Node) bool {
		// Look for any statement nodes
		switch n.(type) {
		case *ast.AssignStmt, *ast.ReturnStmt, *ast.IfStmt, *ast.ForStmt,
			*ast.ExprStmt, *ast.DeclStmt, *ast.SwitchStmt:
			hasCode = true
			return false // Stop inspection
		}
		return true
	})

	return hasCode
}

// tryCompile attempts to compile a Go file
//
// Returns:
//   - bool: true if compiles successfully
//   - string: error message if compilation failed
func (pv *PatternValidator) tryCompile(filePath string) (bool, string) {
	cmd := exec.Command("go", "build", "-o", os.DevNull, filePath)
	output, err := cmd.CombinedOutput()

	if err != nil {
		return false, string(output)
	}

	return true, ""
}

// generateTestCodeWithError creates minimal test code that reproduces the error
//
// This is a simplified version - in production, you'd want to extract context
// from the original error location and reconstruct it properly.
func generateTestCodeWithError(pattern *Pattern) string {
	// For now, create a minimal package with the error pattern
	// In production, this would use the error context from pattern extraction
	return fmt.Sprintf(`package main

import "fmt"

func main() {
	// Error pattern: %s
	// This should fail to compile
	var err error
	if err != nil {
		return // Missing return value - common error
	}
	fmt.Println("done")
}
`, pattern.ErrorSig)
}

// applyPatternSolution applies pattern's solution to error code
//
// This is simplified - production version would:
//  1. Parse error code AST
//  2. Locate error location using pattern.ErrorSig
//  3. Apply solution at that location
//  4. Generate fixed code
//
// For now, we just replace the error pattern with the solution.
func applyPatternSolution(errorCode string, pattern *Pattern) string {
	// Simple string replacement (production would use AST manipulation)
	// This is a placeholder - real implementation would be more sophisticated

	// For demonstration, we'll just insert the solution before the error
	lines := strings.Split(errorCode, "\n")
	var fixed []string

	for _, line := range lines {
		if strings.Contains(line, "Missing return value") {
			// Apply solution
			fixed = append(fixed, "\t"+pattern.SolutionCode)
		}
		fixed = append(fixed, line)
	}

	return strings.Join(fixed, "\n")
}

// Cleanup removes all test files
func (pv *PatternValidator) Cleanup() error {
	return os.RemoveAll(pv.testDir)
}
