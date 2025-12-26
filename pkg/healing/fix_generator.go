package healing

import (
	"context"
	"fmt"
	"strings"
	"time"

	"github.com/google/uuid"
)

// FixGenerator generates surgical fixes from pattern matches
type FixGenerator struct {
	// Future: could inject PatternDB here if needed
}

// NewFixGenerator creates a new fix generator
func NewFixGenerator() *FixGenerator {
	return &FixGenerator{}
}

// GenerateFix creates a Fix object from a pattern match and error
// This is the main entry point for fix generation
func (g *FixGenerator) GenerateFix(
	error CompilationError,
	match PatternMatch,
) (*Fix, error) {
	// Adapt pattern solution to error context
	adaptedSolution := AdaptSolutionToContext(match.Pattern, error)

	// Determine what kind of fix this is
	fixType := DetermineFixType(error, match.Pattern)

	// Extract original code at error location
	originalCode := extractLineFromContext(error.Context, error.LineNumber)

	// Determine imports needed
	var importsToAdd []string
	if fixType == ADD_IMPORT {
		// For ADD_IMPORT fixes, extract from error message
		varName := ExtractVariableName(error.ErrorMessage, error.Context)
		if varName != "value" { // Not fallback
			importsToAdd = []string{varName}
		}
	} else {
		// For other fixes, detect from solution code
		importsToAdd = ExtractRequiredImports(adaptedSolution, error.Context.Imports)
	}

	// Detect indentation
	indentation := 0
	if len(error.Context.SurroundingLines) > 0 {
		_, indentation = DetectIndentation(error.Context.SurroundingLines)
	}

	// Generate human-readable rationale
	rationale := generateFixRationale(match, error)

	fix := &Fix{
		ID:              uuid.New().String(),
		ErrorID:         fmt.Sprintf("%s:%d", error.FilePath, error.LineNumber),
		PatternID:       match.Pattern.ID,
		MatchScore:      match.CombinedScore,
		FixType:         fixType,
		TargetFile:      error.FilePath,
		TargetLine:      error.LineNumber,
		TargetColumn:    error.Column,
		OriginalCode:    originalCode,
		ReplacementCode: adaptedSolution,
		Indentation:     indentation,
		ImportsToAdd:    importsToAdd,
		Confidence:      match.CombinedScore, // Use combined score as confidence
		Rationale:       rationale,
		CreatedAt:       time.Now(),
	}

	return fix, nil
}

// GenerateVariants creates multiple fix variants for swarm testing
// Used for MEDIUM confidence matches where we want to try different approaches
func (g *FixGenerator) GenerateVariants(
	error CompilationError,
	matches []PatternMatch,
	numVariants int,
) ([]*Fix, error) {
	var fixes []*Fix

	// Take top N matches and generate fixes
	count := numVariants
	if count > len(matches) {
		count = len(matches)
	}

	for i := 0; i < count; i++ {
		fix, err := g.GenerateFix(error, matches[i])
		if err != nil {
			continue // Skip failed generations
		}
		fixes = append(fixes, fix)
	}

	return fixes, nil
}

// DetermineFixType analyzes error and pattern to determine fix type
func DetermineFixType(error CompilationError, pattern Pattern) FixType {
	errorMsg := strings.ToLower(error.ErrorMessage)

	// Check for specific error patterns
	switch {
	case strings.Contains(errorMsg, "undefined"):
		// Undefined variable/function/package
		if strings.Contains(errorMsg, "undefined:") {
			// Could be missing import
			return ADD_IMPORT
		}
		return REPLACE_LINE

	case strings.Contains(errorMsg, "missing return"):
		// Need to add return statement
		return ADD_LINE

	case strings.Contains(errorMsg, "cannot use"):
		// Type mismatch - need conversion
		return REPLACE_LINE

	case strings.Contains(errorMsg, "declared and not used"):
		// Unused variable - either remove or use it
		if strings.Contains(pattern.SolutionCode, "return") {
			return REPLACE_LINE // Fix by using it
		}
		return REMOVE_LINE

	case strings.Contains(errorMsg, "syntax error"):
		// Syntax issue - highest priority
		return REPLACE_LINE

	case strings.Contains(errorMsg, "if err != nil") || strings.Contains(errorMsg, "error"):
		// Missing error handling
		return ADD_LINE

	case strings.Contains(errorMsg, "import") && strings.Contains(errorMsg, "not used"):
		// Unused import
		return REMOVE_LINE

	case strings.Contains(errorMsg, "too many") || strings.Contains(errorMsg, "too few"):
		// Wrong number of arguments/return values
		return REPLACE_LINE

	case strings.Contains(errorMsg, "type mismatch"):
		// Type error
		return REPLACE_LINE

	default:
		// Generic replacement
		return REPLACE_LINE
	}
}

// extractLineFromContext gets the line at the error location
func extractLineFromContext(context ErrorContext, lineNumber int) string {
	// If we have surrounding lines, try to extract the specific line
	// This is a simplified version - real implementation would need line mapping
	if len(context.SurroundingLines) > 0 {
		// Assume surrounding lines are centered around error
		// (5 before, 5 after, so middle one is the error)
		middle := len(context.SurroundingLines) / 2
		if middle < len(context.SurroundingLines) {
			return context.SurroundingLines[middle]
		}
		return context.SurroundingLines[0]
	}
	return "" // Will be populated by actual file reading in Wave 3
}

// generateFixRationale creates human-readable explanation for the fix
func generateFixRationale(match PatternMatch, error CompilationError) string {
	var parts []string

	// Start with match reasoning
	if match.MatchRationale != "" {
		parts = append(parts, match.MatchRationale)
	} else {
		parts = append(parts, fmt.Sprintf(
			"Matched pattern #%d with %.1f%% confidence",
			match.Pattern.ID,
			match.CombinedScore*100,
		))
	}

	// Add pattern explanation
	if match.Pattern.Explanation != "" {
		parts = append(parts, match.Pattern.Explanation)
	}

	// Add confidence assessment
	switch {
	case match.CombinedScore >= 0.90:
		parts = append(parts, "HIGH confidence - strongly recommended")
	case match.CombinedScore >= 0.80:
		parts = append(parts, "HIGH confidence - recommended")
	case match.CombinedScore >= 0.70:
		parts = append(parts, "MEDIUM confidence - verify before applying")
	case match.CombinedScore >= 0.60:
		parts = append(parts, "MEDIUM confidence - manual review suggested")
	default:
		parts = append(parts, "LOW confidence - human verification required")
	}

	return strings.Join(parts, ". ")
}

// FormatFix returns a human-readable representation of the fix
func (f *Fix) FormatFix() string {
	var sb strings.Builder

	sb.WriteString(fmt.Sprintf("Fix #%s\n", f.ID[:8])) // Short ID
	sb.WriteString(fmt.Sprintf("  Error: %s\n", f.ErrorID))
	sb.WriteString(fmt.Sprintf("  Type: %s\n", f.FixType))
	sb.WriteString(fmt.Sprintf("  Confidence: %.1f%%\n", f.Confidence*100))

	if len(f.ImportsToAdd) > 0 {
		sb.WriteString(fmt.Sprintf("  Imports to Add: %v\n", f.ImportsToAdd))
	}

	sb.WriteString("\n  Original:\n")
	sb.WriteString(fmt.Sprintf("    %s\n", strings.TrimSpace(f.OriginalCode)))

	sb.WriteString("\n  Replacement:\n")
	for _, line := range strings.Split(f.ReplacementCode, "\n") {
		sb.WriteString(fmt.Sprintf("    %s\n", line))
	}

	sb.WriteString(fmt.Sprintf("\n  Rationale: %s\n", f.Rationale))

	return sb.String()
}

// ValidateFix checks if a fix is ready for application
func (f *Fix) ValidateFix() error {
	if f.TargetFile == "" {
		return fmt.Errorf("fix has no target file")
	}
	if f.TargetLine <= 0 {
		return fmt.Errorf("fix has invalid target line: %d", f.TargetLine)
	}
	if f.ReplacementCode == "" && f.FixType != REMOVE_LINE {
		return fmt.Errorf("fix has no replacement code")
	}
	if f.Confidence < 0.0 || f.Confidence > 1.0 {
		return fmt.Errorf("fix has invalid confidence: %f", f.Confidence)
	}
	return nil
}

// ApplyFix applies a fix to the actual codebase
// This performs the NON-IDEMPOTENT file modification
func (g *FixGenerator) ApplyFix(fix *Fix) error {
	// Placeholder for future implementation
	return fmt.Errorf("ApplyFix not yet implemented - will be added in Wave 7.3")
}

// GenerateFixWithLLM generates a fix using LLM with harmonic retry
//
// Uses harmonic timing to prevent thundering herd when multiple LLM requests
// hit the API simultaneously.
//
// Parameters:
//   - ctx: Context for cancellation
//   - error: Compilation error to fix
//   - maxAttempts: Maximum LLM retry attempts (default: 5)
//
// Returns:
//   - Generated fix (if successful)
//   - Error if all attempts failed
//
// Example:
//
//	gen := NewFixGenerator()
//	fix, err := gen.GenerateFixWithLLM(ctx, compError, 5)
func (g *FixGenerator) GenerateFixWithLLM(
	ctx context.Context,
	compErr CompilationError,
	maxAttempts int,
) (*Fix, error) {
	// Placeholder: LLM integration not yet implemented
	return nil, fmt.Errorf("LLM integration not yet implemented")
}

// ByConfidence implements sort.Interface for []Fix based on confidence
type ByConfidence []*Fix

func (a ByConfidence) Len() int           { return len(a) }
func (a ByConfidence) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByConfidence) Less(i, j int) bool { return a[i].Confidence > a[j].Confidence } // Descending
