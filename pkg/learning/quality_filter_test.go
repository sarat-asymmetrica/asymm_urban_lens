// Package learning implements Ananta's self-healing pattern database and error classification
//
// Quality Filter Tests
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"strings"
	"testing"
)

func TestQualityFilter_FilterPattern_TooSimple(t *testing.T) {
	filter := NewQualityFilter()

	pattern := &Pattern{
		SolutionCode: "", // Empty
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected for empty solution")
	}
	if !strings.Contains(reason, "empty") {
		t.Errorf("Expected reason to mention 'empty', got %s", reason)
	}
}

func TestQualityFilter_FilterPattern_TooComplex(t *testing.T) {
	filter := NewQualityFilter()

	// Create solution with 25 lines (exceeds max of 20)
	lines := make([]string, 25)
	for i := range lines {
		lines[i] = "code line"
	}
	solution := strings.Join(lines, "\n")

	pattern := &Pattern{
		SolutionCode: solution,
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected for being too complex")
	}
	if !strings.Contains(reason, "complex") {
		t.Errorf("Expected reason to mention 'complex', got %s", reason)
	}
}

func TestQualityFilter_FilterPattern_LowConfidence(t *testing.T) {
	filter := NewQualityFilter()

	pattern := &Pattern{
		SolutionCode: "import \"foo\"\nfunc Bar() {}",
		Confidence:   0.10, // Below 0.30 threshold
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected for low confidence")
	}
	if !strings.Contains(reason, "confidence") {
		t.Errorf("Expected reason to mention 'confidence', got %s", reason)
	}
}

func TestQualityFilter_FilterPattern_OnlyWhitespace(t *testing.T) {
	filter := NewQualityFilter()

	pattern := &Pattern{
		SolutionCode: "   \n\t\n   ", // Only whitespace
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected for whitespace-only solution")
	}
	// Whitespace-only counts as "too simple" (0 non-empty lines)
	// This is acceptable - we just want it rejected
	if !strings.Contains(reason, "simple") && !strings.Contains(reason, "whitespace") {
		t.Errorf("Expected reason to mention 'simple' or 'whitespace', got %s", reason)
	}
}

func TestQualityFilter_FilterPattern_TooProjectSpecific(t *testing.T) {
	filter := NewQualityFilter()

	pattern := &Pattern{
		SolutionCode: "path := \"/home/user/myproject/data.json\"",
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected for project-specific paths")
	}
	if !strings.Contains(reason, "project-specific") {
		t.Errorf("Expected reason to mention 'project-specific', got %s", reason)
	}
}

func TestQualityFilter_FilterPattern_ValidPattern(t *testing.T) {
	filter := NewQualityFilter()

	pattern := &Pattern{
		SolutionCode: "import \"fmt\"\nfunc Bar() {\n\tfmt.Println(\"hello\")\n}",
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if !passes {
		t.Errorf("Expected pattern to pass, but was rejected: %s", reason)
	}
	if reason != "" {
		t.Errorf("Expected empty reason for passing pattern, got %s", reason)
	}
}

func TestQualityFilter_IsGeneric_WithAbsolutePath(t *testing.T) {
	filter := NewQualityFilter()

	tests := []struct {
		code     string
		expected bool
	}{
		{"/home/user/file.go", false},
		{"/users/admin/data.json", false},
		{"c:\\windows\\system32", false},
		{"/opt/myapp/config", false},
		{"/var/log/app.log", false},
		{"localhost:8080", false},
		{"127.0.0.1", false},
		{".env", false},
		{"config.yaml", false},
		{"settings.json", false},
		{"import \"foo\"\nfunc Bar() {}", true}, // Generic code
	}

	for _, test := range tests {
		pattern := &Pattern{SolutionCode: test.code}
		result := filter.IsGeneric(pattern)
		if result != test.expected {
			t.Errorf("IsGeneric(%s) = %v, expected %v", test.code, result, test.expected)
		}
	}
}

func TestQualityFilter_IsGeneric_WithSecrets(t *testing.T) {
	filter := NewQualityFilter()

	secretCodes := []string{
		"password = \"secret123\"",
		"api_key = \"abc123\"",
		"SECRET = \"sensitive\"",
		"token = \"xyz789\"",
	}

	for _, code := range secretCodes {
		pattern := &Pattern{SolutionCode: code}
		if filter.IsGeneric(pattern) {
			t.Errorf("IsGeneric should reject pattern with secrets: %s", code)
		}
	}
}

func TestQualityFilter_SetMinComplexity(t *testing.T) {
	filter := NewQualityFilter()
	filter.SetMinComplexity(5)

	pattern := &Pattern{
		SolutionCode: "line1\nline2\nline3", // 3 lines
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected (below min complexity)")
	}
	if !strings.Contains(reason, "simple") {
		t.Errorf("Expected reason to mention 'simple', got %s", reason)
	}
}

func TestQualityFilter_SetMaxComplexity(t *testing.T) {
	filter := NewQualityFilter()
	filter.SetMaxComplexity(2)

	pattern := &Pattern{
		SolutionCode: "line1\nline2\nline3", // 3 lines
		Confidence:   0.50,
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected (exceeds max complexity)")
	}
	if !strings.Contains(reason, "complex") {
		t.Errorf("Expected reason to mention 'complex', got %s", reason)
	}
}

func TestQualityFilter_SetMinConfidence(t *testing.T) {
	filter := NewQualityFilter()
	filter.SetMinConfidence(0.70)

	pattern := &Pattern{
		SolutionCode: "import \"foo\"",
		Confidence:   0.50, // Below new threshold
	}

	passes, reason := filter.FilterPattern(pattern)
	if passes {
		t.Error("Expected pattern to be rejected (below min confidence)")
	}
	if !strings.Contains(reason, "confidence") {
		t.Errorf("Expected reason to mention 'confidence', got %s", reason)
	}
}

func TestNewQualityFilter(t *testing.T) {
	filter := NewQualityFilter()

	if filter == nil {
		t.Fatal("NewQualityFilter returned nil")
	}

	if filter.minComplexity != 1 {
		t.Errorf("Expected minComplexity 1, got %d", filter.minComplexity)
	}
	if filter.maxComplexity != 20 {
		t.Errorf("Expected maxComplexity 20, got %d", filter.maxComplexity)
	}
	if filter.minConfidence != 0.30 {
		t.Errorf("Expected minConfidence 0.30, got %.2f", filter.minConfidence)
	}
}
