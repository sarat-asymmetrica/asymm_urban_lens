package healing

import (
	"regexp"
	"strings"
)

// AdaptSolutionToContext transforms a pattern solution to match error context
// This is where the surgical precision happens - replace placeholders,
// match indentation, extract names from error messages
func AdaptSolutionToContext(pattern Pattern, error CompilationError) string {
	solution := pattern.SolutionCode

	// Extract actual names from error context
	varName := ExtractVariableName(error.ErrorMessage, error.Context)
	typeName := ExtractTypeName(error.ErrorMessage, error.Context)
	funcName := ExtractFunctionName(error.Context)
	pkgName := error.Context.PackageName

	// Replace placeholders with actual values
	solution = strings.ReplaceAll(solution, "<VAR>", varName)
	solution = strings.ReplaceAll(solution, "<TYPE>", typeName)
	solution = strings.ReplaceAll(solution, "<FUNC>", funcName)
	solution = strings.ReplaceAll(solution, "<PKG>", pkgName)

	// Match indentation to surrounding code
	if len(error.Context.SurroundingLines) > 0 {
		solution = MatchIndentation(solution, error.Context.SurroundingLines)
	}

	return solution
}

// ExtractVariableName extracts variable name from error message or context
// Examples:
//   - "undefined: fmt" -> "fmt"
//   - "cannot use x (type int)" -> "x"
//   - "declared and not used: err" -> "err"
func ExtractVariableName(errorMessage string, context ErrorContext) string {
	// Common error patterns with variable names
	patterns := []string{
		`undefined:\s+(\w+)`,            // undefined: varName
		`cannot use (\w+)`,              // cannot use varName
		`declared and not used:\s+(\w+)`, // declared and not used: varName
		`(\w+) declared (and )?not used`, // varName declared not used
		`undeclared name:\s+(\w+)`,      // undeclared name: varName
	}

	for _, pattern := range patterns {
		re := regexp.MustCompile(pattern)
		if matches := re.FindStringSubmatch(errorMessage); len(matches) > 1 {
			return matches[1]
		}
	}

	// Fallback: look for identifier-like words in error message
	re := regexp.MustCompile(`\b([a-z][a-zA-Z0-9_]*)\b`)
	if matches := re.FindStringSubmatch(errorMessage); len(matches) > 1 {
		return matches[1]
	}

	// Generic fallback
	return "value"
}

// ExtractTypeName extracts type name from error message or context
// Examples:
//   - "cannot use x (type int)" -> "int"
//   - "incompatible type string" -> "string"
//   - "expected *User, got User" -> "User"
func ExtractTypeName(errorMessage string, context ErrorContext) string {
	// Common type patterns (order matters - most specific first)
	patterns := []string{
		`\(type ([a-z]\w+)\)`,          // (type int)
		`incompatible type (\w+)`,      // incompatible type string
		`expected ([*\w]+),`,           // expected *Type,
		`cannot convert .* to (\w+)`,   // cannot convert X to Type
		`type ([A-Z]\w+)`,              // type TypeName
		`^type (\w+)`,                  // type string (at start)
	}

	for _, pattern := range patterns {
		re := regexp.MustCompile(pattern)
		if matches := re.FindStringSubmatch(errorMessage); len(matches) > 1 {
			return strings.TrimPrefix(matches[1], "*") // Remove pointer prefix
		}
	}

	// Generic fallback
	return "interface{}"
}

// ExtractFunctionName gets function name from error context
func ExtractFunctionName(context ErrorContext) string {
	if context.FunctionName != "" {
		return context.FunctionName
	}
	return "main" // Generic fallback
}

// MatchIndentation matches solution code to surrounding code's indentation
// Detects tabs vs spaces and applies consistent indentation
func MatchIndentation(solution string, surroundingLines []string) string {
	// Detect indentation type and size (for future use in more advanced matching)
	_, _ = DetectIndentation(surroundingLines)

	// Find the most common indentation level (excluding shallow function declarations)
	// This handles nested code properly - we want the actual code context, not func level
	var indents []string
	for _, line := range surroundingLines {
		trimmed := strings.TrimLeft(line, " \t")
		if len(trimmed) > 0 && len(line) > len(trimmed) {
			indent := line[:len(line)-len(trimmed)]
			// Collect all indents >= 4 spaces (at least one level deep)
			if len(indent) >= 4 {
				indents = append(indents, indent)
			}
		}
	}

	// Use deepest indent (most common context for error fixes)
	var baseIndent string
	if len(indents) > 0 {
		baseIndent = indents[0]
		for _, indent := range indents[1:] {
			if len(indent) > len(baseIndent) {
				baseIndent = indent
			}
		}
	}

	// If solution is multi-line, apply indentation to each line
	lines := strings.Split(solution, "\n")
	for i, line := range lines {
		trimmed := strings.TrimLeft(line, " \t")
		if len(trimmed) > 0 {
			// Apply base indentation
			lines[i] = baseIndent + trimmed
		}
	}

	return strings.Join(lines, "\n")
}

// DetectIndentation analyzes surrounding lines to determine indentation style
// Returns: ("tab", 1) or ("space", N) where N is number of spaces
func DetectIndentation(lines []string) (indentType string, indentSize int) {
	tabCount := 0
	spaceCount := 0
	var spaceSizes []int

	for _, line := range lines {
		if len(line) == 0 {
			continue
		}

		// Check first character
		if line[0] == '\t' {
			tabCount++
		} else if line[0] == ' ' {
			// Count leading spaces
			spaces := 0
			for _, ch := range line {
				if ch == ' ' {
					spaces++
				} else {
					break
				}
			}
			if spaces > 0 {
				spaceCount++
				spaceSizes = append(spaceSizes, spaces)
			}
		}
	}

	// Tabs win if more common
	if tabCount > spaceCount {
		return "tab", 1
	}

	// Detect most common space count (usually 2 or 4)
	if len(spaceSizes) > 0 {
		// Find mode (most common value)
		counts := make(map[int]int)
		for _, size := range spaceSizes {
			counts[size]++
		}

		maxCount := 0
		modeSize := 4 // Default to 4 if unclear
		for size, count := range counts {
			if count > maxCount {
				maxCount = count
				modeSize = size
			}
		}

		return "space", modeSize
	}

	// Default fallback
	return "space", 4
}

// ReplacePlaceholders is a comprehensive placeholder replacement function
// Handles all common placeholders in pattern solutions
func ReplacePlaceholders(solution string, context map[string]string) string {
	for placeholder, value := range context {
		solution = strings.ReplaceAll(solution, placeholder, value)
	}
	return solution
}

// ExtractRequiredImports analyzes solution code to find needed imports
// Returns imports that are used in solution but not in current file
func ExtractRequiredImports(solution string, currentImports []string) []string {
	var needed []string

	// Common package usage patterns
	patterns := map[string]string{
		`fmt\.`:           "fmt",
		`errors\.`:        "errors",
		`context\.`:       "context",
		`sync\.`:          "sync",
		`time\.`:          "time",
		`strings\.`:       "strings",
		`strconv\.`:       "strconv",
		`io\.`:            "io",
		`os\.`:            "os",
		`json\.`:          "encoding/json",
		`http\.`:          "net/http",
		`sql\.`:           "database/sql",
		`log\.`:           "log",
	}

	// Check if solution uses packages not in current imports
	for pattern, pkg := range patterns {
		re := regexp.MustCompile(pattern)
		if re.MatchString(solution) {
			// Check if already imported
			alreadyImported := false
			for _, imp := range currentImports {
				if strings.Contains(imp, pkg) {
					alreadyImported = true
					break
				}
			}
			if !alreadyImported {
				needed = append(needed, pkg)
			}
		}
	}

	return needed
}
