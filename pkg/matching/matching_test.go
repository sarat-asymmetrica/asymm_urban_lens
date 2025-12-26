// Package matching tests
package matching

import (
	"testing"

	"github.com/asymmetrica/urbanlens/pkg/vqc"
)

func TestFuzzyMatcher_ExactMatch(t *testing.T) {
	matcher := NewFuzzyMatcher()

	// Create pattern
	pattern := NewPattern("test1", "error_check", "if err != nil { return err }", "error_handling", "Go")

	patterns := []Pattern{*pattern}

	// Exact match input
	input := "if err != nil { return err }"

	matches, err := matcher.Match(input, patterns)
	if err != nil {
		t.Fatalf("Match failed: %v", err)
	}

	if len(matches) == 0 {
		t.Fatal("Expected at least one match")
	}

	// Should be exact match
	if matches[0].Score != 1.0 {
		t.Errorf("Expected score 1.0 for exact match, got %f", matches[0].Score)
	}

	if matches[0].Context.AlgorithmUsed != "exact" {
		t.Errorf("Expected exact algorithm, got %s", matches[0].Context.AlgorithmUsed)
	}
}

func TestFuzzyMatcher_FuzzyMatch(t *testing.T) {
	matcher := NewFuzzyMatcher()

	// Create pattern
	pattern := NewPattern("test2", "error_check", "if err != nil { return err }", "error_handling", "Go")
	patterns := []Pattern{*pattern}

	// Similar but not exact input
	input := "if error != nil { return error }"

	matches, err := matcher.Match(input, patterns)
	if err != nil {
		t.Fatalf("Match failed: %v", err)
	}

	if len(matches) == 0 {
		t.Fatal("Expected at least one fuzzy match")
	}

	// Should be fuzzy match with high score
	if matches[0].Score < 0.80 {
		t.Errorf("Expected high similarity for fuzzy match, got %f", matches[0].Score)
	}
}

func TestFuzzyMatcher_DigitalRootFilter(t *testing.T) {
	config := DefaultMatcherConfig()
	config.UseDigitalRootFilter = true
	matcher := NewFuzzyMatcherWithConfig(config)

	// Create patterns with different lengths
	pattern1 := NewPattern("p1", "short", "if x { y }", "control", "Go")
	pattern2 := NewPattern("p2", "long", "if something != nil { return fmt.Errorf('error') }", "error", "Go")

	patterns := []Pattern{*pattern1, *pattern2}

	// Input matches pattern1 length
	input := "if a { b }"

	matches, err := matcher.Match(input, patterns)
	if err != nil {
		t.Fatalf("Match failed: %v", err)
	}

	// Digital root filter should have eliminated pattern2
	// Verify at least one match found
	if len(matches) == 0 {
		t.Fatal("Expected at least one match")
	}
}

func TestStructuralSimilarity(t *testing.T) {
	tests := []struct {
		s1       string
		s2       string
		expected float64
		minScore float64
	}{
		{"hello", "hello", 1.0, 1.0},
		{"hello", "hallo", 0.8, 0.7},
		{"", "", 1.0, 1.0},
		{"abc", "xyz", 0.0, 0.0},
	}

	for _, tt := range tests {
		score := StructuralSimilarity(tt.s1, tt.s2)
		if tt.expected > 0 && score != tt.expected {
			t.Errorf("StructuralSimilarity(%q, %q) = %f, want %f", tt.s1, tt.s2, score, tt.expected)
		}
		if score < tt.minScore {
			t.Errorf("StructuralSimilarity(%q, %q) = %f, want >= %f", tt.s1, tt.s2, score, tt.minScore)
		}
	}
}

func TestQuaternionSimilarity(t *testing.T) {
	q1 := vqc.NewQuaternion(1, 0, 0, 0).Normalize()
	q2 := vqc.NewQuaternion(1, 0, 0, 0).Normalize()

	// Identical quaternions
	sim := QuaternionSimilarity(q1, q2)
	if sim != 1.0 {
		t.Errorf("QuaternionSimilarity(identical) = %f, want 1.0", sim)
	}

	// Orthogonal quaternions
	q3 := vqc.NewQuaternion(0, 1, 0, 0).Normalize()
	sim = QuaternionSimilarity(q1, q3)
	if sim < 0.0 || sim > 1.0 {
		t.Errorf("QuaternionSimilarity out of range [0,1]: %f", sim)
	}
}

func TestNormalizeSolution(t *testing.T) {
	tests := []struct {
		input    string
		contains []string
	}{
		{
			input:    `if err != nil { return fmt.Errorf("error: %v", err) }`,
			contains: []string{"if", "<VAR>", "nil", "return", "<FUNC>", "<LITERAL>"},
		},
		{
			input:    `for i := 0; i < 10; i++ { sum += i }`,
			contains: []string{"for", "<VAR>", "<LITERAL>"},
		},
	}

	for _, tt := range tests {
		normalized := NormalizeSolution(tt.input)
		for _, expected := range tt.contains {
			if !containsString(normalized, expected) {
				t.Errorf("NormalizeSolution(%q) missing %q, got: %q", tt.input, expected, normalized)
			}
		}
	}
}

func TestTemplateEngine_Instantiate(t *testing.T) {
	te := NewTemplateEngine()

	template := "if {{var}} != nil { return {{func}}({{var}}) }"
	bindings := map[string]interface{}{
		"var":  "err",
		"func": "fmt.Errorf",
	}

	result, err := te.Instantiate(template, bindings)
	if err != nil {
		t.Fatalf("Instantiate failed: %v", err)
	}

	expected := "if err != nil { return fmt.Errorf(err) }"
	if result != expected {
		t.Errorf("Instantiate result = %q, want %q", result, expected)
	}
}

func TestTemplateEngine_ExtractBindings(t *testing.T) {
	te := NewTemplateEngine()

	template := "if {{var}} != nil { return {{func}}({{var}}) }"
	input := "if err != nil { return fmt.Errorf(err) }"

	bindings, err := te.ExtractBindings(template, input)
	if err != nil {
		t.Fatalf("ExtractBindings failed: %v", err)
	}

	if bindings["var"] != "err" {
		t.Errorf("bindings[var] = %v, want 'err'", bindings["var"])
	}

	if bindings["func"] != "fmt.Errorf" {
		t.Errorf("bindings[func] = %v, want 'fmt.Errorf'", bindings["func"])
	}
}

func TestPatternRanker_RankPatterns(t *testing.T) {
	ranker := NewPatternRanker()

	// Create patterns with different qualities
	p1 := NewPattern("p1", "high_quality", "code1", "cat1", "Go")
	p1.Confidence = 0.9
	p1.Frequency = 100

	p2 := NewPattern("p2", "low_quality", "code2", "cat1", "Go")
	p2.Confidence = 0.3
	p2.Frequency = 5

	p3 := NewPattern("p3", "medium_quality", "code3", "cat1", "Go")
	p3.Confidence = 0.6
	p3.Frequency = 50

	patterns := []*Pattern{p2, p3, p1} // Intentionally out of order

	ranked := ranker.RankPatterns(patterns)

	// Should be ranked: p1 > p3 > p2
	if ranked[0].Pattern.ID != "p1" {
		t.Errorf("Rank 1 should be p1, got %s", ranked[0].Pattern.ID)
	}
	if ranked[2].Pattern.ID != "p2" {
		t.Errorf("Rank 3 should be p2, got %s", ranked[2].Pattern.ID)
	}

	// Verify ranks are assigned correctly
	if ranked[0].Rank != 1 {
		t.Errorf("Top pattern rank = %d, want 1", ranked[0].Rank)
	}
}

func TestPatternRanker_FilterByQuality(t *testing.T) {
	ranker := NewPatternRanker()

	p1 := NewPattern("p1", "high", "code1", "cat1", "Go")
	p1.Confidence = 0.9
	p1.Frequency = 100

	p2 := NewPattern("p2", "low", "code2", "cat1", "Go")
	p2.Confidence = 0.2
	p2.Frequency = 1

	patterns := []*Pattern{p1, p2}

	filtered := ranker.FilterByQuality(patterns, 0.5)

	if len(filtered) != 1 {
		t.Errorf("Expected 1 pattern after filtering, got %d", len(filtered))
	}

	if filtered[0].ID != "p1" {
		t.Errorf("Filtered pattern should be p1, got %s", filtered[0].ID)
	}
}

func TestAreSimilar(t *testing.T) {
	p1 := NewPattern("p1", "test", "if err != nil { return err }", "error", "Go")
	p2 := NewPattern("p2", "test", "if err != nil { return err }", "error", "Go")
	p3 := NewPattern("p3", "diff", "for i := 0; i < n; i++ { }", "loop", "Go")

	// Exact match
	similar, score := AreSimilar(p1, p2)
	if !similar || score != 1.0 {
		t.Errorf("AreSimilar(identical) = (%v, %f), want (true, 1.0)", similar, score)
	}

	// Different patterns
	similar, score = AreSimilar(p1, p3)
	if similar && score >= 0.85 {
		t.Errorf("AreSimilar(different) = (%v, %f), should be dissimilar", similar, score)
	}
}

func TestGetStandardPatterns(t *testing.T) {
	patterns := GetStandardPatterns("Go")

	if len(patterns) < 3 {
		t.Errorf("Expected at least 3 standard patterns, got %d", len(patterns))
	}

	// Verify categories
	categories := make(map[string]bool)
	for _, p := range patterns {
		categories[p.Category] = true
	}

	expectedCategories := []string{"error_handling", "validation", "control_flow"}
	for _, cat := range expectedCategories {
		if !categories[cat] {
			t.Errorf("Missing expected category: %s", cat)
		}
	}
}

func TestEncodeToQuaternion(t *testing.T) {
	q := EncodeToQuaternion("test string")

	// Verify it's normalized
	norm := q.Norm()
	if norm < 0.99 || norm > 1.01 {
		t.Errorf("Encoded quaternion norm = %f, want ~1.0", norm)
	}
}

func BenchmarkFuzzyMatcher_Match(b *testing.B) {
	matcher := NewFuzzyMatcher()

	// Create 100 patterns
	patterns := make([]Pattern, 100)
	for i := 0; i < 100; i++ {
		pattern := NewPattern(
			string(rune(i)),
			"test",
			"if err != nil { return err }",
			"error",
			"Go",
		)
		patterns[i] = *pattern
	}

	input := "if error != nil { return error }"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = matcher.Match(input, patterns)
	}
}

func BenchmarkStructuralSimilarity(b *testing.B) {
	s1 := "if err != nil { return fmt.Errorf(\"error: %v\", err) }"
	s2 := "if error != nil { return fmt.Errorf(\"err: %v\", error) }"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = StructuralSimilarity(s1, s2)
	}
}

func BenchmarkQuaternionSimilarity(b *testing.B) {
	q1 := vqc.NewQuaternion(1, 0, 0, 0).Normalize()
	q2 := vqc.NewQuaternion(0.9, 0.1, 0.1, 0.1).Normalize()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = QuaternionSimilarity(q1, q2)
	}
}

// Helper function
func containsString(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && containsSubstring(s, substr))
}

func containsSubstring(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
