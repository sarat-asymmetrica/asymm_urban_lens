// ═══════════════════════════════════════════════════════════════════════════
// WILLIAMS BATCHING OPTIMALITY PROOF - TESTS & VALIDATION
// ═══════════════════════════════════════════════════════════════════════════

package lean

import (
	"math"
	"strings"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// TEST 1: OPTIMAL BATCH SIZE COMPUTATION
// ═══════════════════════════════════════════════════════════════════════════

func TestGetOptimalBatchSize(t *testing.T) {
	tests := []struct {
		name     string
		input    int
		expected int
	}{
		{"Edge case: t=1", 1, 1},
		{"Small: t=100", 100, 100}, // Clamped to min
		{"Vedic scale: t=108,000", 108_000, 5_494}, // √108000 × log₂(108001) ≈ 5494
		{"GPU scale: t=432,000", 432_000, 10_000}, // Clamped to max (actual ~11K)
		{"1 million", 1_000_000, 10_000}, // Clamped to max
		{"10 million", 10_000_000, 10_000}, // Clamped to max
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := GetOptimalBatchSize(tt.input)

			// Allow ±1% tolerance for rounding
			tolerance := int(math.Max(1.0, float64(tt.expected)*0.01))

			if abs(result-tt.expected) > tolerance {
				t.Errorf("GetOptimalBatchSize(%d) = %d, want %d (±%d)",
					tt.input, result, tt.expected, tolerance)
			}
		})
	}
}

func abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 2: VEDIC SCALE VALIDATION (108,000)
// ═══════════════════════════════════════════════════════════════════════════

func TestVedicScaleProof(t *testing.T) {
	theorem := VedicScaleProof()

	// Validate input
	if theorem.InputSize != 108_000 {
		t.Errorf("Expected input size 108,000, got %d", theorem.InputSize)
	}

	// Validate batch size (should be ~5,494 with +1 formula)
	expectedBatch := 5_494
	tolerance := int(float64(expectedBatch) * 0.02) // 2% tolerance
	if abs(theorem.OptimalBatch-expectedBatch) > tolerance {
		t.Errorf("Expected batch ~%d, got %d", expectedBatch, theorem.OptimalBatch)
	}

	// Validate memory savings (should be ~94-95%)
	if theorem.MemorySavings < 94.0 || theorem.MemorySavings > 96.0 {
		t.Errorf("Expected memory savings 94-96%%, got %.2f%%", theorem.MemorySavings)
	}

	// Validate speedup (should be ~20x)
	if theorem.Speedup < 15.0 || theorem.Speedup > 25.0 {
		t.Errorf("Expected speedup 15-25x, got %.2fx", theorem.Speedup)
	}

	// Validate proofs exist
	if theorem.LowerBoundProofText == "" {
		t.Error("Lower bound proof is empty")
	}
	if theorem.UpperBoundProofText == "" {
		t.Error("Upper bound proof is empty")
	}
	if theorem.OptimalityProofText == "" {
		t.Error("Optimality proof is empty")
	}

	// Validate status
	if !theorem.Validated {
		t.Error("Theorem should be validated")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 3: PROOF CONTENT VALIDATION
// ═══════════════════════════════════════════════════════════════════════════

func TestProofContent(t *testing.T) {
	theorem := NewWilliamsTheorem(108_000)

	// Lower bound proof should mention key concepts
	lowerProof := strings.ToLower(theorem.LowerBoundProofText)
	requiredTerms := []string{
		"communication complexity",
		"yao",
		"k-sum",
		"pebbl", // Match "Pebbling" or "pebble"
	}

	for _, term := range requiredTerms {
		if !strings.Contains(lowerProof, term) {
			t.Errorf("Lower bound proof missing term: %s", term)
		}
	}

	// Upper bound proof should mention key concepts
	upperProof := strings.ToLower(theorem.UpperBoundProofText)
	requiredTerms = []string{
		"williams",
		"algorithm",
		"production",
	}

	for _, term := range requiredTerms {
		if !strings.Contains(upperProof, term) {
			t.Errorf("Upper bound proof missing term: %s", term)
		}
	}

	// Optimality proof should mention tight bound
	optimalityProof := strings.ToLower(theorem.OptimalityProofText)
	requiredTerms = []string{
		"optimal",
		"lower",
		"upper",
	}

	for _, term := range requiredTerms {
		if !strings.Contains(optimalityProof, term) {
			t.Errorf("Optimality proof missing term: %s", term)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARK: OPTIMAL BATCH SIZE COMPUTATION
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkGetOptimalBatchSize(b *testing.B) {
	sizes := []int{1_000, 10_000, 100_000, 1_000_000}

	for _, size := range sizes {
		b.Run(string(rune(size)), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				GetOptimalBatchSize(size)
			}
		})
	}
}
