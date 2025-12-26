package lean

import (
	"strings"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// ENTITY EXTRACTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestExtractEntities(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		wantType string
		wantName string
	}{
		{
			name:     "constant extraction",
			input:    "The speed of light c = 299792458",
			wantType: "constant",
			wantName: "c",
		},
		{
			name:     "variable extraction",
			input:    "For all x : ℕ, x + 0 = x",
			wantType: "variable",
			wantName: "x",
		},
		{
			name:     "function extraction",
			input:    "The function square(n) returns n squared",
			wantType: "function",
			wantName: "square",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			entities := ExtractEntities(tt.input)
			found := false
			for _, e := range entities {
				if e.Type == tt.wantType && e.Name == tt.wantName {
					found = true
					break
				}
			}
			if !found {
				t.Errorf("Expected entity type=%s name=%s, got entities: %+v",
					tt.wantType, tt.wantName, entities)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// PATTERN SELECTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestSelectPatternForInsight(t *testing.T) {
	tests := []struct {
		name        string
		insight     string
		wantPattern string
	}{
		{
			name:        "conservation law",
			insight:     "Energy is conserved in a closed system",
			wantPattern: "conservation",
		},
		{
			name:        "transitivity",
			insight:     "If A > B and B > C then A > C",
			wantPattern: "transitivity",
		},
		{
			name:        "induction",
			insight:     "We can prove this by induction on n",
			wantPattern: "induction",
		},
		{
			name:        "equivalence",
			insight:     "A number is even if and only if it's divisible by 2",
			wantPattern: "equivalence",
		},
		{
			name:        "contradiction",
			insight:     "Assume the opposite leads to contradiction",
			wantPattern: "contradiction",
		},
		{
			name:        "existence",
			insight:     "There exists a prime number greater than 100",
			wantPattern: "construction",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			pattern := SelectPatternForInsight(tt.insight)
			if pattern.Name != tt.wantPattern {
				t.Errorf("Expected pattern %s, got %s", tt.wantPattern, pattern.Name)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// TRANSLATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestTranslateToLean_Conservation(t *testing.T) {
	statement := "Energy is conserved in a closed thermodynamic system"
	context := &ConversationContext{
		Domain: "physics",
		DefinedTerms: map[string]string{
			"energy": "ℝ",
			"system": "ThermodynamicSystem",
		},
	}

	result, err := TranslateToLean(statement, context)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	// Check that it's a conservation theorem
	if result.Pattern.Name != "conservation" {
		t.Errorf("Expected conservation pattern, got %s", result.Pattern.Name)
	}

	// Check that Lean code contains expected elements
	leanCode := result.LeanCode
	expectedElements := []string{
		"theorem",
		"PhysicalSystem",
		"energy",
		":= by",
	}

	for _, elem := range expectedElements {
		if !strings.Contains(leanCode, elem) {
			t.Errorf("Expected Lean code to contain '%s', got:\n%s", elem, leanCode)
		}
	}
}

func TestTranslateToLean_Transitivity(t *testing.T) {
	statement := "If temperature A is greater than B and B is greater than C, then A is greater than C"

	result, err := TranslateToLean(statement, nil)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	if result.Pattern.Name != "transitivity" {
		t.Errorf("Expected transitivity pattern, got %s", result.Pattern.Name)
	}

	leanCode := result.LeanCode
	if !strings.Contains(leanCode, "trans") {
		t.Errorf("Transitivity proof should mention 'trans' tactic")
	}
}

func TestTranslateToLean_Induction(t *testing.T) {
	statement := "For all natural numbers n, we can prove by induction that the sum formula holds"

	result, err := TranslateToLean(statement, nil)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	if result.Pattern.Name != "induction" {
		t.Errorf("Expected induction pattern, got %s", result.Pattern.Name)
	}

	leanCode := result.LeanCode
	expectedElements := []string{
		"induction",
		"zero",
		"succ",
		"ih",
	}

	for _, elem := range expectedElements {
		if !strings.Contains(leanCode, elem) {
			t.Errorf("Induction proof should contain '%s', got:\n%s", elem, leanCode)
		}
	}
}

func TestTranslateToLean_Equivalence(t *testing.T) {
	statement := "A number is even if and only if it is divisible by 2"

	result, err := TranslateToLean(statement, nil)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	if result.Pattern.Name != "equivalence" {
		t.Errorf("Expected equivalence pattern, got %s", result.Pattern.Name)
	}

	leanCode := result.LeanCode
	if !strings.Contains(leanCode, "↔") && !strings.Contains(leanCode, "Iff") {
		t.Errorf("Equivalence proof should contain '↔', got:\n%s", leanCode)
	}

	if !strings.Contains(leanCode, "constructor") {
		t.Errorf("Equivalence proof should use 'constructor' tactic")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// THEOREM NAME GENERATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestGenerateTheoremName(t *testing.T) {
	tests := []struct {
		statement string
		want      string
	}{
		{
			statement: "Energy is conserved in closed systems",
			want:      "energy_conserved_closed_systems",
		},
		{
			statement: "The sum of even numbers is even",
			want:      "sum_even_numbers_even",
		},
		{
			statement: "Prime numbers are infinite",
			want:      "prime_numbers_infinite",
		},
	}

	for _, tt := range tests {
		t.Run(tt.statement, func(t *testing.T) {
			got := generateTheoremName(tt.statement)
			if got != tt.want {
				t.Errorf("generateTheoremName(%q) = %q, want %q",
					tt.statement, got, tt.want)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// DOMAIN INFERENCE TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestInferDomain(t *testing.T) {
	tests := []struct {
		statement string
		want      string
	}{
		{
			statement: "Energy and momentum are conserved",
			want:      "physics",
		},
		{
			statement: "The probability of two independent events",
			want:      "probability",
		},
		{
			statement: "A circle has constant curvature",
			want:      "geometry",
		},
		{
			statement: "Prime numbers have unique factorization",
			want:      "number_theory",
		},
		{
			statement: "The function is continuous at x = 0",
			want:      "analysis",
		},
	}

	for _, tt := range tests {
		t.Run(tt.statement, func(t *testing.T) {
			got := inferDomain(tt.statement)
			if got != tt.want {
				t.Errorf("inferDomain(%q) = %q, want %q",
					tt.statement, got, tt.want)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// MATHEMATICAL STRUCTURE DETECTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestDetectMathematicalStructure(t *testing.T) {
	tests := []struct {
		name     string
		text     string
		features []string
	}{
		{
			name:     "universal quantifier",
			text:     "For all x, P(x) holds",
			features: []string{"universal_quantifier"},
		},
		{
			name:     "existential quantifier",
			text:     "There exists x such that P(x)",
			features: []string{"existential_quantifier"},
		},
		{
			name:     "biconditional",
			text:     "P if and only if Q",
			features: []string{"biconditional"},
		},
		{
			name:     "implication",
			text:     "If P then Q",
			features: []string{"implication"},
		},
		{
			name:     "induction",
			text:     "We prove this by induction",
			features: []string{"induction"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			structure := DetectMathematicalStructure(tt.text)
			for _, feature := range tt.features {
				if !structure[feature] {
					t.Errorf("Expected to detect feature '%s' in '%s'",
						feature, tt.text)
				}
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HYPOTHESIS-CONCLUSION EXTRACTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestExtractHypothesisConclusion(t *testing.T) {
	tests := []struct {
		name      string
		statement string
		wantHyp   string
		wantConcl string
	}{
		{
			name:      "if-then",
			statement: "If x > 0 then x + 1 > 1",
			wantHyp:   "x > 0",
			wantConcl: "x + 1 > 1",
		},
		{
			name:      "implies",
			statement: "x > 5 implies x > 0",
			wantHyp:   "x > 5",
			wantConcl: "x > 0",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			hyp, concl := extractHypothesisConclusion(tt.statement)
			if hyp != tt.wantHyp {
				t.Errorf("Hypothesis: got %q, want %q", hyp, tt.wantHyp)
			}
			if concl != tt.wantConcl {
				t.Errorf("Conclusion: got %q, want %q", concl, tt.wantConcl)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CONFIDENCE SCORING TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestTranslationConfidence(t *testing.T) {
	tests := []struct {
		name          string
		statement     string
		minConfidence float64
	}{
		{
			name:          "clear conservation",
			statement:     "Energy is conserved in closed systems",
			minConfidence: 0.6,
		},
		{
			name:          "clear equivalence",
			statement:     "x is even if and only if 2 divides x",
			minConfidence: 0.6,
		},
		{
			name:          "ambiguous",
			statement:     "Something happens sometimes",
			minConfidence: 0.0, // Low confidence for vague statements
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, err := TranslateToLean(tt.statement, nil)
			if err != nil {
				t.Fatalf("Translation failed: %v", err)
			}

			if result.Confidence < tt.minConfidence {
				t.Errorf("Expected confidence >= %f, got %f for statement: %s",
					tt.minConfidence, result.Confidence, tt.statement)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// INTEGRATION TEST: FULL PIPELINE
// ═══════════════════════════════════════════════════════════════════════════

func TestFullTranslationPipeline(t *testing.T) {
	// Simulate a conversation about roti thermodynamics
	context := &ConversationContext{
		Domain: "physics",
		DefinedTerms: map[string]string{
			"energy":      "ℝ",
			"temperature": "ℝ",
			"steam":       "State",
		},
		PreviousStatements: []string{
			"Water requires energy to vaporize",
		},
		Assumptions: []string{
			"The system is at atmospheric pressure",
		},
	}

	statement := "When roti is covered, heat is trapped and prevents steam formation"

	result, err := TranslateToLean(statement, context)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	// Verify the result
	t.Logf("Generated Lean code:\n%s", result.LeanCode)
	t.Logf("Pattern: %s", result.Pattern.Name)
	t.Logf("Confidence: %.2f", result.Confidence)
	t.Logf("Suggestions: %v", result.Suggestions)

	// Basic sanity checks
	if result.LeanCode == "" {
		t.Error("Expected non-empty Lean code")
	}

	if result.Pattern == nil {
		t.Error("Expected a proof pattern to be selected")
	}

	if len(result.Suggestions) == 0 {
		t.Error("Expected some suggestions to be generated")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// EDGE CASES
// ═══════════════════════════════════════════════════════════════════════════

func TestTranslateToLean_EmptyStatement(t *testing.T) {
	result, err := TranslateToLean("", nil)
	if err != nil {
		t.Fatalf("Should handle empty statement gracefully: %v", err)
	}

	if result.Confidence > 0.3 {
		t.Error("Expected low confidence for empty statement")
	}
}

func TestTranslateToLean_ComplexStatement(t *testing.T) {
	statement := `For all natural numbers n, if n is greater than 1,
	               then there exists a prime p that divides n`

	_, err := TranslateToLean(statement, nil)
	if err != nil {
		t.Fatalf("Should handle complex statement: %v", err)
	}

	// Should detect multiple structures
	structure := DetectMathematicalStructure(statement)
	if !structure["universal_quantifier"] {
		t.Error("Should detect universal quantifier")
	}
	if !structure["existential_quantifier"] {
		t.Error("Should detect existential quantifier")
	}
	if !structure["implication"] {
		t.Error("Should detect implication")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkTranslateToLean(b *testing.B) {
	statement := "Energy is conserved in closed thermodynamic systems"
	context := &ConversationContext{
		Domain: "physics",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = TranslateToLean(statement, context)
	}
}

func BenchmarkExtractEntities(b *testing.B) {
	text := "For all x : ℕ, if x > 0 then there exists y : ℕ such that y = x + 1"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = ExtractEntities(text)
	}
}

func BenchmarkSelectPattern(b *testing.B) {
	insight := "If A implies B and B implies C then A implies C"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = SelectPatternForInsight(insight)
	}
}
