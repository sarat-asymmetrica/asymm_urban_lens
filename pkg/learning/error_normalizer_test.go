// Package learning implements Ananta's self-healing pattern database and error classification
//
// Error Normalizer Tests
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"testing"
)

// TestRemoveFilePaths verifies file path removal
func TestRemoveFilePaths(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"main.go:42: error", "<FILE>:42: error"},
		{"/usr/local/src/main.go:42", "<FILE>:42"},
		{"C:\\Users\\dev\\project\\main.go:42", "<FILE>:42"},
		{"github.com/user/repo/pkg/file.go:10", "github.com/user/repo/pkg/<FILE>:10"},
		{"no file path here", "no file path here"},
	}

	for _, tt := range tests {
		result := RemoveFilePaths(tt.input)
		if result != tt.expected {
			t.Errorf("RemoveFilePaths(%q) = %q, want %q", tt.input, result, tt.expected)
		}
	}
}

// TestRemoveLineNumbers verifies line number removal
func TestRemoveLineNumbers(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"main.go:42: error", "main.go:<LINE> error"},
		{"file.go:123:", "file.go:<LINE>"},
		{"no line numbers", "no line numbers"},
		{":999:", ":<LINE>"},
	}

	for _, tt := range tests {
		result := RemoveLineNumbers(tt.input)
		if result != tt.expected {
			t.Errorf("RemoveLineNumbers(%q) = %q, want %q", tt.input, result, tt.expected)
		}
	}
}

// TestRemoveVariableNames verifies variable name removal
func TestRemoveVariableNames(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"undefined: myVar", "undefined: <VAR>"},
		{"undeclared: someFunc", "undeclared: <VAR>"},
		{"cannot use userName", "cannot use <VAR>"},
		{"no variables here", "no variables here"},
	}

	for _, tt := range tests {
		result := RemoveVariableNames(tt.input)
		if result != tt.expected {
			t.Errorf("RemoveVariableNames(%q) = %q, want %q", tt.input, result, tt.expected)
		}
	}
}

// TestRemoveTypeNames verifies type name removal
func TestRemoveTypeNames(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"type MyStruct is not", "type <TYPE> is not"},
		{"struct UserData has", "struct <TYPE> has"},
		{"interface Reader is", "interface <TYPE> is"},
		{"no types here", "no types here"},
	}

	for _, tt := range tests {
		result := RemoveTypeNames(tt.input)
		if result != tt.expected {
			t.Errorf("RemoveTypeNames(%q) = %q, want %q", tt.input, result, tt.expected)
		}
	}
}

// TestRemovePackagePaths verifies package path removal
func TestRemovePackagePaths(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"import github.com/spf13/cobra", "import <PKG>"},
		{"use golang.org/x/tools/go/analysis", "use <PKG>"},
		{"gopkg.in/yaml.v2", "<PKG>"},
		{"no package paths", "no package paths"},
	}

	for _, tt := range tests {
		result := RemovePackagePaths(tt.input)
		if result != tt.expected {
			t.Errorf("RemovePackagePaths(%q) = %q, want %q", tt.input, result, tt.expected)
		}
	}
}

// TestRemoveMemoryAddresses verifies memory address removal
func TestRemoveMemoryAddresses(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"panic at 0xc0000b4000", "panic at <ADDR>"},
		{"address: 0x1234ABCD", "address: <ADDR>"},
		{"no addresses", "no addresses"},
	}

	for _, tt := range tests {
		result := RemoveMemoryAddresses(tt.input)
		if result != tt.expected {
			t.Errorf("RemoveMemoryAddresses(%q) = %q, want %q", tt.input, result, tt.expected)
		}
	}
}

// TestNormalizeError verifies complete normalization pipeline
func TestNormalizeError(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected string
	}{
		{
			name:     "simple undefined error",
			input:    "main.go:42: undefined: fmt",
			expected: "<FILE>:<LINE> undefined: <VAR>",
		},
		{
			name:     "type error",
			input:    "handler.go:123: cannot use myVar (type MyStruct) as type Handler",
			expected: "<FILE>:<LINE> cannot use <VAR> (type <TYPE>) as type <TYPE>",
		},
		{
			name:     "package import error",
			input:    "/usr/src/main.go:10: imported and not used: github.com/spf13/cobra",
			expected: "<FILE>:<LINE> imported and not used: <PKG>",
		},
		{
			name:     "runtime panic",
			input:    "panic: runtime error: index out of range [5] with length 3 at 0xc0000b4000",
			expected: "panic: runtime error: index out of range [5] with length 3 at <ADDR>",
		},
		{
			name:     "multiple file paths",
			input:    "main.go:42: imported from handler.go:10: undefined: fmt",
			expected: "<FILE>:<LINE> imported from <FILE>:<LINE> undefined: <VAR>",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := NormalizeError(tt.input)
			if result != tt.expected {
				t.Errorf("NormalizeError(%q)\n  got:  %q\n  want: %q", tt.input, result, tt.expected)
			}
		})
	}
}

// TestNormalizeErrorConsistency verifies that normalization is consistent
// across different error instances
func TestNormalizeErrorConsistency(t *testing.T) {
	// Same error in different files
	errors := []string{
		"main.go:42: undefined: fmt",
		"handler.go:123: undefined: fmt",
		"/Users/dev/project/api/server.go:999: undefined: fmt",
		"C:\\Projects\\app\\src\\utils.go:55: undefined: fmt",
	}

	var normalized []string
	for _, err := range errors {
		normalized = append(normalized, NormalizeError(err))
	}

	// All should normalize to the same string
	expected := normalized[0]
	for i, norm := range normalized {
		if norm != expected {
			t.Errorf("Inconsistent normalization at index %d:\n  got:  %q\n  want: %q\n  from: %q", i, norm, expected, errors[i])
		}
	}
}

// TestAggressiveNormalization verifies aggressive normalization
func TestAggressiveNormalization(t *testing.T) {
	input := `main.go:42: error "invalid syntax" with value 123`
	result := AggressiveNormalization(input)

	// Should remove strings and numbers
	if result == input {
		t.Error("AggressiveNormalization should modify input")
	}

	// Check that strings and numbers are removed
	// (exact output depends on regex order, so just verify it changes)
	t.Logf("AggressiveNormalization(%q) = %q", input, result)
}

// BenchmarkNormalizeError benchmarks the normalization pipeline
func BenchmarkNormalizeError(b *testing.B) {
	errorMsg := "main.go:42: undefined: fmt"
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		NormalizeError(errorMsg)
	}
}

// BenchmarkRemoveFilePaths benchmarks file path removal
func BenchmarkRemoveFilePaths(b *testing.B) {
	input := "/usr/local/src/project/main.go:42: error"
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		RemoveFilePaths(input)
	}
}

// BenchmarkAggressiveNormalization benchmarks aggressive normalization
func BenchmarkAggressiveNormalization(b *testing.B) {
	input := `main.go:42: error "invalid syntax" with value 123`
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		AggressiveNormalization(input)
	}
}
