// Package parsers implements language-specific error parsing
package parsers

import (
	"bufio"
	"fmt"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
)

// GoErrorParser parses Go compiler errors
type GoErrorParser struct{}

// ParseErrors parses Go compiler output and extracts all errors
//
// Go error format:
//   ./path/file.go:123:45: error message
//   path/file.go:56:12: cannot use x (type int) as type string
//
// Regex pattern: (\.?[^:]+):(\d+):(\d+):\s+(.+)
func (p *GoErrorParser) ParseErrors(compilerOutput string) ([]CompilationError, error) {
	var errors []CompilationError

	// Regex to match Go error format
	// Group 1: file path, Group 2: line, Group 3: column, Group 4: message
	errorRegex := regexp.MustCompile(`^(\.?[^:]+\.go):(\d+):(\d+):\s+(.+)$`)

	scanner := bufio.NewScanner(strings.NewReader(compilerOutput))
	for scanner.Scan() {
		line := scanner.Text()

		// Skip empty lines and informational messages
		if strings.TrimSpace(line) == "" {
			continue
		}

		// Match error pattern
		matches := errorRegex.FindStringSubmatch(line)
		if matches == nil {
			// Not an error line (might be context or suggestions)
			continue
		}

		// Extract components
		filePath := matches[1]
		lineNum, _ := strconv.Atoi(matches[2])
		column, _ := strconv.Atoi(matches[3])
		message := matches[4]

		// Convert relative path to absolute if needed
		absPath, err := filepath.Abs(filePath)
		if err != nil {
			absPath = filePath // Fall back to original path
		}

		// Create error object
		compErr := CompilationError{
			FilePath:     absPath,
			LineNumber:   lineNum,
			Column:       column,
			ErrorMessage: message,
		}

		errors = append(errors, compErr)
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("failed to scan compiler output: %w", err)
	}

	return errors, nil
}
