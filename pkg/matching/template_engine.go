// Package matching implements pattern template engine
//
// Template Engine: Pattern templates with variable substitution
// Author: Zen Gardener (Wave 3)
package matching

import (
	"fmt"
	"regexp"
	"strings"
)

// TemplateEngine handles pattern template instantiation and matching
type TemplateEngine struct {
	patterns []Pattern
}

// NewTemplateEngine creates a new template engine
func NewTemplateEngine() *TemplateEngine {
	return &TemplateEngine{
		patterns: []Pattern{},
	}
}

// RegisterPattern registers a pattern template
func (te *TemplateEngine) RegisterPattern(pattern Pattern) {
	te.patterns = append(te.patterns, pattern)
}

// RegisterPatterns registers multiple pattern templates
func (te *TemplateEngine) RegisterPatterns(patterns []Pattern) {
	te.patterns = append(te.patterns, patterns...)
}

// Instantiate creates a concrete pattern from template with bindings
// Example: "if {{var}} != nil { return {{func}}({{var}}) }"
//          with bindings {"var": "err", "func": "fmt.Errorf"}
//          => "if err != nil { return fmt.Errorf(err) }"
func (te *TemplateEngine) Instantiate(template string, bindings map[string]interface{}) (string, error) {
	result := template

	// Replace each binding
	for key, value := range bindings {
		placeholder := fmt.Sprintf("{{%s}}", key)
		valueStr := fmt.Sprintf("%v", value)
		result = strings.ReplaceAll(result, placeholder, valueStr)
	}

	// Check for unreplaced placeholders
	if hasPlaceholders(result) {
		unreplaced := extractPlaceholders(result)
		return "", fmt.Errorf("unreplaced placeholders: %v", unreplaced)
	}

	return result, nil
}

// ExtractBindings extracts variable bindings from input matching template
// This is the inverse of Instantiate - given a template and concrete input,
// extract the variable values.
//
// Example:
//   Template: "if {{var}} != nil { return {{func}}({{var}}) }"
//   Input:    "if err != nil { return fmt.Errorf(err) }"
//   Returns:  {"var": "err", "func": "fmt.Errorf"}
func (te *TemplateEngine) ExtractBindings(template, input string) (map[string]interface{}, error) {
	bindings := make(map[string]interface{})

	// Convert template to regex pattern
	pattern := templateToRegex(template)
	re, err := regexp.Compile(pattern)
	if err != nil {
		return nil, fmt.Errorf("failed to compile template regex: %w", err)
	}

	// Extract matches
	matches := re.FindStringSubmatch(input)
	if matches == nil {
		return nil, fmt.Errorf("input does not match template")
	}

	// Get placeholder names from template
	placeholders := extractPlaceholders(template)

	// Map matches to placeholders
	if len(matches)-1 != len(placeholders) {
		return nil, fmt.Errorf("placeholder count mismatch: expected %d, got %d", len(placeholders), len(matches)-1)
	}

	for i, placeholder := range placeholders {
		bindings[placeholder] = matches[i+1] // matches[0] is full match
	}

	return bindings, nil
}

// MatchTemplate finds patterns that match the template structure
func (te *TemplateEngine) MatchTemplate(input string) ([]Match, error) {
	var matches []Match

	for _, pattern := range te.patterns {
		bindings, err := te.ExtractBindings(pattern.Template, input)
		if err != nil {
			continue // Pattern doesn't match
		}

		// Calculate match score based on binding quality
		score := te.scoreBindings(bindings)

		matches = append(matches, Match{
			Pattern:     &pattern,
			Score:       score,
			Bindings:    bindings,
			Explanation: fmt.Sprintf("Template match with %d bindings", len(bindings)),
			Confidence:  pattern.Confidence,
		})
	}

	return matches, nil
}

// scoreBindings calculates quality score for bindings
func (te *TemplateEngine) scoreBindings(bindings map[string]interface{}) float64 {
	if len(bindings) == 0 {
		return 0.0
	}

	// Score based on:
	// 1. Number of bindings (more = more specific)
	// 2. Non-empty bindings
	// 3. Identifier validity

	nonEmpty := 0
	validIdentifiers := 0

	for _, value := range bindings {
		valueStr := fmt.Sprintf("%v", value)
		if valueStr != "" {
			nonEmpty++
			if isValidIdentifier(valueStr) {
				validIdentifiers++
			}
		}
	}

	if len(bindings) == 0 {
		return 0.0
	}

	// Score formula
	score := (float64(nonEmpty) / float64(len(bindings))) * 0.5
	score += (float64(validIdentifiers) / float64(len(bindings))) * 0.5

	return score
}

// hasPlaceholders checks if string contains {{...}} placeholders
func hasPlaceholders(s string) bool {
	return strings.Contains(s, "{{") && strings.Contains(s, "}}")
}

// extractPlaceholders extracts all {{...}} placeholders from template
func extractPlaceholders(template string) []string {
	re := regexp.MustCompile(`\{\{([^}]+)\}\}`)
	matches := re.FindAllStringSubmatch(template, -1)

	var placeholders []string
	seen := make(map[string]bool)

	for _, match := range matches {
		if len(match) > 1 {
			placeholder := strings.TrimSpace(match[1])
			if !seen[placeholder] {
				placeholders = append(placeholders, placeholder)
				seen[placeholder] = true
			}
		}
	}

	return placeholders
}

// templateToRegex converts template with {{...}} to regex pattern
// Example: "if {{var}} != nil" => "if (.+?) != nil"
func templateToRegex(template string) string {
	// Escape regex special chars (except {})
	escaped := regexp.QuoteMeta(template)

	// Replace escaped placeholders with capture groups
	// QuoteMeta converts {{ to \{\{ and }} to \}\}
	re := regexp.MustCompile(`\\\{\\\{[^}]+\\\}\\\}`)
	pattern := re.ReplaceAllString(escaped, `(.+?)`)

	// Anchor to full string match
	return "^" + pattern + "$"
}

// isValidIdentifier checks if string is a valid identifier
func isValidIdentifier(s string) bool {
	if s == "" {
		return false
	}

	// Must start with letter or underscore
	if !isLetter(rune(s[0])) && s[0] != '_' {
		return false
	}

	// Rest must be letters, digits, or underscores
	for _, r := range s[1:] {
		if !isLetter(r) && !isDigit(r) && r != '_' {
			return false
		}
	}

	return true
}

// isLetter checks if rune is a letter
func isLetter(r rune) bool {
	return (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z')
}

// isDigit checks if rune is a digit
func isDigit(r rune) bool {
	return r >= '0' && r <= '9'
}

// CreateErrorHandlingPattern creates a standard error handling pattern
func CreateErrorHandlingPattern(id, language string) Pattern {
	var template string
	switch language {
	case "Go":
		template = `if {{var}} != nil {
	return {{returnType}}({{args}})
}`
	case "TypeScript", "JavaScript":
		template = `if ({{var}}) {
	throw new {{errorType}}({{message}})
}`
	case "Python":
		template = `if {{var}}:
	raise {{exceptionType}}({{message}})`
	case "Rust":
		template = `if let Err({{var}}) = {{result}} {
	return Err({{var}})
}`
	default:
		template = "if {{var}} { return {{error}} }"
	}

	pattern := NewPattern(id, "error_handling", template, "error_handling", language)
	pattern.Confidence = 0.80 // High confidence for standard pattern

	return *pattern
}

// CreateNilCheckPattern creates a nil/null check pattern
func CreateNilCheckPattern(id, language string) Pattern {
	var template string
	switch language {
	case "Go":
		template = "if {{var}} == nil { {{action}} }"
	case "TypeScript", "JavaScript":
		template = "if ({{var}} === null || {{var}} === undefined) { {{action}} }"
	case "Python":
		template = "if {{var}} is None: {{action}}"
	case "Rust":
		template = "if {{var}}.is_none() { {{action}} }"
	default:
		template = "if {{var}} == null { {{action}} }"
	}

	pattern := NewPattern(id, "nil_check", template, "validation", language)
	pattern.Confidence = 0.85

	return *pattern
}

// CreateLoopPattern creates a standard loop pattern
func CreateLoopPattern(id, language string) Pattern {
	var template string
	switch language {
	case "Go":
		template = "for {{index}}, {{value}} := range {{collection}} { {{body}} }"
	case "TypeScript", "JavaScript":
		template = "for (const {{value}} of {{collection}}) { {{body}} }"
	case "Python":
		template = "for {{value}} in {{collection}}: {{body}}"
	case "Rust":
		template = "for {{value}} in {{collection}} { {{body}} }"
	default:
		template = "for {{item}} in {{collection}} { {{body}} }"
	}

	pattern := NewPattern(id, "loop", template, "control_flow", language)
	pattern.Confidence = 0.75

	return *pattern
}

// GetStandardPatterns returns a collection of standard patterns for a language
func GetStandardPatterns(language string) []Pattern {
	return []Pattern{
		CreateErrorHandlingPattern("error_handling_1", language),
		CreateNilCheckPattern("nil_check_1", language),
		CreateLoopPattern("loop_1", language),
	}
}
