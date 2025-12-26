// Package verification implements compilation verification and regression detection
//
// Output Parser: Parse compiler output into structured errors
// Author: Agent 4.1 (Dr. Liam O'Connor - Formal Verification, Oxford)
// Created: 2025-11-07
// Ported: 2025-12-26 (Urban Lens Integration)
package verification

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/asymm_urbanlens/urbanlens/pkg/reasoning"
)

// OutputParser converts compiler output to structured errors
type OutputParser struct {
	language string
}

// NewOutputParser creates parser for specified language
func NewOutputParser(language string) *OutputParser {
	return &OutputParser{
		language: language,
	}
}

// ParseOutput extracts errors from compiler output
func (op *OutputParser) ParseOutput(output *BuildOutput) ([]reasoning.CompilationError, error) {
	if output == nil {
		return nil, fmt.Errorf("nil build output")
	}

	// If compilation succeeded, return empty slice
	if output.Success {
		return []reasoning.CompilationError{}, nil
	}

	// Use combined output (stdout + stderr)
	compilerOutput := output.Stdout
	if compilerOutput == "" {
		compilerOutput = output.Stderr
	}

	// Parse based on language
	var errors []reasoning.CompilationError
	var parseErr error

	switch strings.ToLower(op.language) {
	case "go", "golang":
		errors, parseErr = op.parseGoErrors(compilerOutput)
	case "rust":
		errors, parseErr = op.parseRustErrors(compilerOutput)
	case "typescript", "ts":
		errors, parseErr = op.parseTypeScriptErrors(compilerOutput)
	default:
		return nil, fmt.Errorf("unsupported language: %s", op.language)
	}

	if parseErr != nil {
		return nil, fmt.Errorf("failed to parse errors: %w", parseErr)
	}

	return errors, nil
}

// parseGoErrors parses Go compiler errors
// Format: ./file.go:123:45: error message
func (op *OutputParser) parseGoErrors(output string) ([]reasoning.CompilationError, error) {
	errors := []reasoning.CompilationError{}
	pattern := regexp.MustCompile(`([^:]+):(\d+):(\d+):\s*(.+)`)

	lines := strings.Split(output, "\n")
	for _, line := range lines {
		matches := pattern.FindStringSubmatch(line)
		if matches != nil && len(matches) >= 5 {
			lineNum, _ := strconv.Atoi(matches[2])
			colNum, _ := strconv.Atoi(matches[3])

			errors = append(errors, reasoning.CompilationError{
				FilePath:     matches[1],
				LineNumber:   lineNum,
				Column:       colNum,
				ErrorMessage: matches[4],
				ErrorType:    "compile",
			})
		}
	}

	return errors, nil
}

// parseRustErrors parses Rust compiler errors
func (op *OutputParser) parseRustErrors(output string) ([]reasoning.CompilationError, error) {
	errors := []reasoning.CompilationError{}
	pattern := regexp.MustCompile(`error.*-->\s*([^:]+):(\d+):(\d+)`)

	lines := strings.Split(output, "\n")
	for i, line := range lines {
		matches := pattern.FindStringSubmatch(line)
		if matches != nil && len(matches) >= 4 {
			lineNum, _ := strconv.Atoi(matches[2])
			colNum, _ := strconv.Atoi(matches[3])

			// Get error message from next line
			errorMsg := ""
			if i+1 < len(lines) {
				errorMsg = strings.TrimSpace(lines[i+1])
			}

			errors = append(errors, reasoning.CompilationError{
				FilePath:     matches[1],
				LineNumber:   lineNum,
				Column:       colNum,
				ErrorMessage: errorMsg,
				ErrorType:    "compile",
			})
		}
	}

	return errors, nil
}

// parseTypeScriptErrors parses TypeScript compiler errors
func (op *OutputParser) parseTypeScriptErrors(output string) ([]reasoning.CompilationError, error) {
	errors := []reasoning.CompilationError{}
	pattern := regexp.MustCompile(`([^(]+)\((\d+),(\d+)\):\s*error\s*TS\d+:\s*(.+)`)

	lines := strings.Split(output, "\n")
	for _, line := range lines {
		matches := pattern.FindStringSubmatch(line)
		if matches != nil && len(matches) >= 5 {
			lineNum, _ := strconv.Atoi(matches[2])
			colNum, _ := strconv.Atoi(matches[3])

			errors = append(errors, reasoning.CompilationError{
				FilePath:     matches[1],
				LineNumber:   lineNum,
				Column:       colNum,
				ErrorMessage: matches[4],
				ErrorType:    "compile",
			})
		}
	}

	return errors, nil
}

// DiffErrors compares before/after error lists
func (op *OutputParser) DiffErrors(
	before []reasoning.CompilationError,
	after []reasoning.CompilationError,
) *ErrorDiff {
	diff := &ErrorDiff{
		Fixed:     []reasoning.CompilationError{},
		New:       []reasoning.CompilationError{},
		Unchanged: []reasoning.CompilationError{},
	}

	// Create maps for O(1) lookup using error signatures
	afterMap := make(map[string]reasoning.CompilationError)
	for _, err := range after {
		sig := errorSignature(err)
		afterMap[sig] = err
	}

	beforeMap := make(map[string]reasoning.CompilationError)
	for _, err := range before {
		sig := errorSignature(err)
		beforeMap[sig] = err
	}

	// Find fixed errors (in before but not in after)
	for _, err := range before {
		sig := errorSignature(err)
		if _, exists := afterMap[sig]; !exists {
			diff.Fixed = append(diff.Fixed, err)
			diff.FixedCount++
		} else {
			diff.Unchanged = append(diff.Unchanged, err)
			diff.UnchangedCount++
		}
	}

	// Find new errors (in after but not in before)
	for _, err := range after {
		sig := errorSignature(err)
		if _, exists := beforeMap[sig]; !exists {
			diff.New = append(diff.New, err)
			diff.NewCount++
		}
	}

	return diff
}

// errorSignature creates unique signature for error matching
// Uses file:line:message for exact matching
func errorSignature(err reasoning.CompilationError) string {
	return fmt.Sprintf("%s:%d:%s", err.FilePath, err.LineNumber, err.ErrorMessage)
}

// IsSameError checks if two errors are the same
func IsSameError(a, b reasoning.CompilationError) bool {
	return errorSignature(a) == errorSignature(b)
}

// CountErrorsByType counts errors by type
func (op *OutputParser) CountErrorsByType(errors []reasoning.CompilationError) map[string]int {
	counts := make(map[string]int)
	for _, err := range errors {
		errType := err.ErrorType
		if errType == "" {
			errType = "unknown"
		}
		counts[errType]++
	}
	return counts
}

// GroupErrorsByFile groups errors by file path
func (op *OutputParser) GroupErrorsByFile(errors []reasoning.CompilationError) map[string][]reasoning.CompilationError {
	groups := make(map[string][]reasoning.CompilationError)
	for _, err := range errors {
		groups[err.FilePath] = append(groups[err.FilePath], err)
	}
	return groups
}
