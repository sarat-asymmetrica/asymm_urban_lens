// Package learning implements Ananta's self-healing pattern database and error classification
//
// Quality Filter: Filters low-quality patterns to maintain DB quality
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"fmt"
	"regexp"
	"strings"
)

// QualityFilter removes noisy/low-quality patterns
type QualityFilter struct {
	minComplexity int     // Min lines changed (default: 1)
	maxComplexity int     // Max lines changed (default: 20)
	minConfidence float64 // Min confidence (default: 0.30)
}

// NewQualityFilter creates a quality filter with default thresholds
func NewQualityFilter() *QualityFilter {
	return &QualityFilter{
		minComplexity: 1,
		maxComplexity: 20,
		minConfidence: 0.30,
	}
}

// FilterPattern determines if pattern is high quality
//
// Returns:
//   - (true, "") if pattern passes quality checks
//   - (false, reason) if pattern is rejected
//
// Rejection criteria:
//   - Solution too simple (<1 line = trivial)
//   - Solution too complex (>20 lines = too specific)
//   - Confidence too low (<0.30)
//   - Solution contains project-specific names
//   - Solution is just whitespace changes
func (qf *QualityFilter) FilterPattern(pattern *Pattern) (bool, string) {
	// Check solution exists
	if pattern.SolutionCode == "" {
		return false, "empty solution"
	}

	// Count non-empty lines
	lines := strings.Split(pattern.SolutionCode, "\n")
	nonEmptyLines := 0
	for _, line := range lines {
		if strings.TrimSpace(line) != "" {
			nonEmptyLines++
		}
	}

	// Check complexity bounds
	if nonEmptyLines < qf.minComplexity {
		return false, fmt.Sprintf("too simple (%d lines, min %d)", nonEmptyLines, qf.minComplexity)
	}
	if nonEmptyLines > qf.maxComplexity {
		return false, fmt.Sprintf("too complex (%d lines, max %d)", nonEmptyLines, qf.maxComplexity)
	}

	// Check confidence
	if pattern.Confidence < qf.minConfidence {
		return false, fmt.Sprintf("confidence too low (%.2f, min %.2f)", pattern.Confidence, qf.minConfidence)
	}

	// Check if only whitespace changes
	if qf.isOnlyWhitespace(pattern.SolutionCode) {
		return false, "only whitespace changes"
	}

	// Check if too project-specific
	if !qf.IsGeneric(pattern) {
		return false, "too project-specific"
	}

	return true, ""
}

// IsGeneric checks if pattern is reusable across projects
//
// Pattern is generic if:
//   - Uses placeholders (<VAR>, <TYPE>, etc.) OR
//   - No hardcoded project names
//   - No absolute paths
//   - No environment-specific config
func (qf *QualityFilter) IsGeneric(pattern *Pattern) bool {
	code := strings.ToLower(pattern.SolutionCode)

	// Check for project-specific indicators
	projectIndicators := []string{
		"/home/",
		"/users/",
		"c:\\",
		"/opt/",
		"/var/",
		"localhost",
		"127.0.0.1",
		".env",
		"config.yaml",
		"settings.json",
	}

	for _, indicator := range projectIndicators {
		if strings.Contains(code, indicator) {
			return false
		}
	}

	// Check for hardcoded credentials/secrets
	secretPatterns := []*regexp.Regexp{
		regexp.MustCompile(`(?i)password\s*=\s*['"][^'"]+['"]`),
		regexp.MustCompile(`(?i)api[_-]?key\s*=\s*['"][^'"]+['"]`),
		regexp.MustCompile(`(?i)secret\s*=\s*['"][^'"]+['"]`),
		regexp.MustCompile(`(?i)token\s*=\s*['"][^'"]+['"]`),
	}

	for _, pattern := range secretPatterns {
		if pattern.MatchString(code) {
			return false
		}
	}

	// Pattern is generic if no red flags found
	return true
}

// isOnlyWhitespace checks if solution is just formatting changes
func (qf *QualityFilter) isOnlyWhitespace(code string) bool {
	// Remove all whitespace
	cleaned := regexp.MustCompile(`\s+`).ReplaceAllString(code, "")

	// If nothing left after removing whitespace, it's only whitespace
	return cleaned == ""
}

// SetMinComplexity configures minimum line count
func (qf *QualityFilter) SetMinComplexity(min int) {
	qf.minComplexity = min
}

// SetMaxComplexity configures maximum line count
func (qf *QualityFilter) SetMaxComplexity(max int) {
	qf.maxComplexity = max
}

// SetMinConfidence configures minimum confidence threshold
func (qf *QualityFilter) SetMinConfidence(min float64) {
	qf.minConfidence = min
}
