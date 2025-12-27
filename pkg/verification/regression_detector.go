// Package verification implements compilation verification and regression detection
//
// Regression Detector: Identify and classify regressions from applied fixes
// Author: Agent 4.1 (Dr. Liam O'Connor - Formal Verification, Oxford)
// Created: 2025-11-07
// Ported: 2025-12-26 (Urban Lens Integration)
package verification

import (
	"strings"

	"github.com/asymmetrica/urbanlens/pkg/reasoning"
)

// RegressionDetector identifies bad fixes
type RegressionDetector struct {
	strictMode bool // If true, treat warnings as regressions
}

// NewRegressionDetector creates detector with specified mode
func NewRegressionDetector(strictMode bool) *RegressionDetector {
	return &RegressionDetector{
		strictMode: strictMode,
	}
}

// DetectRegressions analyzes error diff for regressions
func (rd *RegressionDetector) DetectRegressions(diff *ErrorDiff) []Regression {
	if diff == nil {
		return []Regression{}
	}

	regressions := make([]Regression, 0, len(diff.New))

	for _, err := range diff.New {
		severity := rd.ClassifySeverity(err)

		// In strict mode, all new errors are regressions
		// In normal mode, only major/critical are regressions
		if rd.strictMode || severity != SeverityMinor {
			regressions = append(regressions, Regression{
				FilePath:     err.FilePath,
				LineNumber:   err.LineNumber,
				ErrorMessage: err.ErrorMessage,
				ErrorType:    err.ErrorType,
				Severity:     severity,
			})
		}
	}

	return regressions
}

// ClassifySeverity determines how bad a regression is
func (rd *RegressionDetector) ClassifySeverity(err reasoning.CompilationError) RegressionSeverity {
	msg := strings.ToLower(err.ErrorMessage)

	// Critical: syntax errors, undefined symbols, cannot compile
	criticalPatterns := []string{
		"syntax error",
		"undefined:",
		"undeclared name",
		"not declared",
		"cannot find",
		"expected declaration",
		"invalid syntax",
	}

	for _, pattern := range criticalPatterns {
		if strings.Contains(msg, pattern) {
			return SeverityCritical
		}
	}

	// Major: type mismatches, missing imports, wrong signatures
	majorPatterns := []string{
		"type mismatch",
		"cannot use",
		"cannot convert",
		"undefined type",
		"missing return",
		"too many arguments",
		"not enough arguments",
		"cannot assign",
	}

	for _, pattern := range majorPatterns {
		if strings.Contains(msg, pattern) {
			return SeverityMajor
		}
	}

	// Minor: warnings, unused variables, deprecations
	minorPatterns := []string{
		"declared and not used",
		"imported and not used",
		"never used",
		"deprecated",
		"warning:",
	}

	for _, pattern := range minorPatterns {
		if strings.Contains(msg, pattern) {
			return SeverityMinor
		}
	}

	// Default to major for unknown error types
	return SeverityMajor
}

// IsAcceptable checks if regression is acceptable trade-off
func (rd *RegressionDetector) IsAcceptable(
	errorsFixed int,
	regressions []Regression,
) bool {
	if len(regressions) == 0 {
		return true // No regressions = always acceptable
	}

	// Count regressions by severity
	critical := 0
	major := 0
	minor := 0

	for _, reg := range regressions {
		switch reg.Severity {
		case SeverityCritical:
			critical++
		case SeverityMajor:
			major++
		case SeverityMinor:
			minor++
		}
	}

	// NEVER accept critical regressions
	if critical > 0 {
		return false
	}

	// Major regressions acceptable only if we fixed significantly more
	// Rule: Fixed errors must be >= 3× major regressions
	if major > 0 {
		return errorsFixed >= (major * 3)
	}

	// Minor regressions acceptable if we fixed more than we introduced
	// Rule: Fixed errors must be > minor regressions
	if minor > 0 {
		return errorsFixed > minor
	}

	return true
}

// CalculateRegressionScore computes regression impact score (0.0 = no regression, 1.0 = catastrophic)
func (rd *RegressionDetector) CalculateRegressionScore(regressions []Regression) float64 {
	if len(regressions) == 0 {
		return 0.0
	}

	// Weight regressions by severity
	// Critical: 1.0, Major: 0.5, Minor: 0.1
	totalImpact := 0.0
	for _, reg := range regressions {
		switch reg.Severity {
		case SeverityCritical:
			totalImpact += 1.0
		case SeverityMajor:
			totalImpact += 0.5
		case SeverityMinor:
			totalImpact += 0.1
		}
	}

	// Normalize by number of regressions (cap at 1.0)
	score := totalImpact / float64(len(regressions))
	if score > 1.0 {
		score = 1.0
	}

	return score
}

// GroupRegressionsBySeverity groups regressions by severity level
func (rd *RegressionDetector) GroupRegressionsBySeverity(regressions []Regression) map[RegressionSeverity][]Regression {
	groups := make(map[RegressionSeverity][]Regression)
	groups[SeverityCritical] = []Regression{}
	groups[SeverityMajor] = []Regression{}
	groups[SeverityMinor] = []Regression{}

	for _, reg := range regressions {
		groups[reg.Severity] = append(groups[reg.Severity], reg)
	}

	return groups
}
