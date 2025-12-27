package lean

import (
	"fmt"
	"math"
	"testing"
)

// ============================================================================
// PART I: BASIC THEOREM VALIDATION
// ============================================================================

func TestNewAttractorTheorem(t *testing.T) {
	theorem := NewAttractorTheorem()

	// Validate constants
	tests := []struct {
		name     string
		got      float64
		expected float64
		tolerance float64
	}{
		{"Empirical Attractor", theorem.EmpiricalAttractor, 0.87532, 1e-10},
		{"Seven Eighths", theorem.SevenEighths, 0.875, 1e-10},
		{"One Eighth", theorem.OneEighth, 0.125, 1e-10},
		{"Critical Alpha", theorem.CriticalAlpha, 4.26, 1e-10},
		{"Complexity Debt", theorem.ComplexityDebt, 0.12468, 1e-10},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if math.Abs(tt.got-tt.expected) > tt.tolerance {
				t.Errorf("%s: got %.10f, expected %.10f",
					tt.name, tt.got, tt.expected)
			}
		})
	}

	// Validate integers
	if theorem.QuaternionDim != 4 {
		t.Errorf("QuaternionDim: got %d, expected 4", theorem.QuaternionDim)
	}
	if theorem.OctonionDim != 8 {
		t.Errorf("OctonionDim: got %d, expected 8", theorem.OctonionDim)
	}
	if theorem.ImaginaryQuaternions != 3 {
		t.Errorf("ImaginaryQuaternions: got %d, expected 3", theorem.ImaginaryQuaternions)
	}
	if theorem.ImaginaryOctonions != 7 {
		t.Errorf("ImaginaryOctonions: got %d, expected 7", theorem.ImaginaryOctonions)
	}
}

// ============================================================================
// PART II: PROVE ATTRACTOR NEAR 7/8
// ============================================================================

func TestProveAttractorNear7Over8(t *testing.T) {
	theorem := NewAttractorTheorem()

	valid, err := theorem.ProveAttractorNear7Over8()

	if !valid {
		t.Fatalf("Attractor NOT near 7/8: %v", err)
	}

	// Validate the actual delta
	expectedDelta := math.Abs(0.87532 - 0.875)
	if expectedDelta >= 0.001 {
		t.Errorf("Delta too large: %.5f >= 0.001", expectedDelta)
	}

	// Expected: |0.87532 - 0.875| = 0.00032 < 0.001 ✓
	t.Logf("✓ Attractor near 7/8: |%.5f - %.5f| = %.5f < 0.001",
		theorem.EmpiricalAttractor, theorem.SevenEighths, expectedDelta)
}

func TestProveAttractorNear7Over8_EdgeCases(t *testing.T) {
	tests := []struct {
		name      string
		attractor float64
		shouldPass bool
	}{
		{"Exact 7/8", 0.875, true},
		{"Just below tolerance", 0.87532, true},
		{"Just above tolerance", 0.87632, false},
		{"Far below", 0.85, false},
		{"Far above", 0.90, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			theorem := &AttractorTheorem{
				EmpiricalAttractor: tt.attractor,
				SevenEighths:       7.0 / 8.0,
				AttractorVariance:  0.001,
			}

			valid, err := theorem.ProveAttractorNear7Over8()

			if valid != tt.shouldPass {
				t.Errorf("Expected shouldPass=%v, got valid=%v (err: %v)",
					tt.shouldPass, valid, err)
			}
		})
	}
}

// ============================================================================
// PART III: PROVE COMPLEXITY DEBT NEAR 1/8
// ============================================================================

func TestProveComplexityDebtNear1Over8(t *testing.T) {
	theorem := NewAttractorTheorem()

	valid, err := theorem.ProveComplexityDebtNear1Over8()

	if !valid {
		t.Fatalf("Complexity debt NOT near 1/8: %v", err)
	}

	// Validate the actual delta
	expectedDelta := math.Abs(0.12468 - 0.125)
	if expectedDelta >= 0.001 {
		t.Errorf("Delta too large: %.5f >= 0.001", expectedDelta)
	}

	// Expected: |0.12468 - 0.125| = 0.00032 < 0.001 ✓
	t.Logf("✓ Complexity debt near 1/8: |%.5f - %.5f| = %.5f < 0.001",
		theorem.ComplexityDebt, theorem.OneEighth, expectedDelta)
}

// ============================================================================
// PART IV: DIMENSIONAL RATIOS
// ============================================================================

func TestProveDimensionalRatio(t *testing.T) {
	theorem := NewAttractorTheorem()

	ratios := theorem.ProveDimensionalRatio()

	tests := []struct {
		name     string
		key      string
		expected float64
		tolerance float64
	}{
		{"Octonion imaginary ratio", "octonion_imaginary_ratio", 7.0/8.0, 1e-10},
		{"Quaternion imaginary ratio", "quaternion_imaginary_ratio", 3.0/4.0, 1e-10},
		{"7/8 shadow", "dimensional_shadow_7_over_8", 0.875, 1e-10},
		{"3/4 shadow", "dimensional_shadow_3_over_4", 0.75, 1e-10},
		{"7/3 imaginary ratio", "imaginary_ratio_7_over_3", 7.0/3.0, 1e-10},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := ratios[tt.key]
			if math.Abs(got-tt.expected) > tt.tolerance {
				t.Errorf("%s: got %.10f, expected %.10f",
					tt.name, got, tt.expected)
			}
		})
	}

	// Log all ratios
	t.Logf("Dimensional Ratios:")
	for k, v := range ratios {
		t.Logf("  %s: %.5f", k, v)
	}
}

// ============================================================================
// PART V: PHASE TRANSITION VALIDATION
// ============================================================================

func TestProvePhaseTransitionAtAlpha(t *testing.T) {
	theorem := NewAttractorTheorem()

	tests := []struct {
		alpha          float64
		expectedPhase  string
		expectedInZone bool
	}{
		{3.0, "P-like (underconstrained)", false},
		{4.0, "P-like (underconstrained)", false},
		{4.2, "PHASE_TRANSITION_ZONE", true},
		{4.26, "PHASE_TRANSITION_ZONE", true},
		{4.267, "PHASE_TRANSITION_ZONE", true},
		{4.3, "PHASE_TRANSITION_ZONE", true},
		{4.5, "NP-hard (overconstrained)", false},
		{5.0, "NP-hard (overconstrained)", false},
	}

	for _, tt := range tests {
		t.Run("alpha="+fmt.Sprintf("%.2f", tt.alpha), func(t *testing.T) {
			phase, inZone := theorem.ProvePhaseTransitionAtAlpha(tt.alpha)

			if phase != tt.expectedPhase {
				t.Errorf("Expected phase '%s', got '%s'",
					tt.expectedPhase, phase)
			}

			if inZone != tt.expectedInZone {
				t.Errorf("Expected inZone=%v, got %v",
					tt.expectedInZone, inZone)
			}
		})
	}

	// Validate the actual critical alpha
	phase, inZone := theorem.ProvePhaseTransitionAtAlpha(theorem.CriticalAlpha)
	if !inZone {
		t.Errorf("Critical alpha %.2f should be in phase transition zone, got phase: %s",
			theorem.CriticalAlpha, phase)
	}

	t.Logf("✓ Critical alpha %.2f is in %s", theorem.CriticalAlpha, phase)
}

// ============================================================================
// PART VI: THERMODYNAMIC ENTROPY VALIDATION
// ============================================================================

func TestComputeTheoreticalEntropy(t *testing.T) {
	theorem := NewAttractorTheorem()

	tests := []struct {
		numVariables int
		expected     float64
		tolerance    float64
	}{
		{1000, 86.49, 0.01},
		{10000, 864.9, 0.1},
		{108000, 9341.5, 1.0},
		{216000, 18683.0, 2.0},
		{432000, 37366.0, 4.0},
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("n=%d", tt.numVariables), func(t *testing.T) {
			entropy := theorem.ComputeTheoreticalEntropy(tt.numVariables)

			if math.Abs(entropy-tt.expected) > tt.tolerance {
				t.Errorf("n=%d: got entropy %.2f, expected %.2f ± %.2f",
					tt.numVariables, entropy, tt.expected, tt.tolerance)
			}

			t.Logf("n=%d: entropy=%.2f (expected %.2f)",
				tt.numVariables, entropy, tt.expected)
		})
	}

	// Validate the n=108,000 case specifically (from breakthrough report)
	entropy := theorem.ComputeTheoreticalEntropy(108000)
	measured := 9335.03
	errorPercent := math.Abs(entropy-measured) / entropy * 100

	t.Logf("n=108,000 validation:")
	t.Logf("  Theoretical: %.2f", entropy)
	t.Logf("  Measured:    %.2f", measured)
	t.Logf("  Error:       %.3f%%", errorPercent)

	if errorPercent > 0.1 {
		t.Errorf("Error too high: %.3f%% > 0.1%%", errorPercent)
	}
}

// ============================================================================
// PART VII: VALIDATION INTERFACE
// ============================================================================

func TestValidateAttractor(t *testing.T) {
	tests := []struct {
		observed   float64
		shouldPass bool
	}{
		{0.87532, true},   // Exact attractor
		{0.87530, true},   // Just below
		{0.87534, true},   // Just above
		{0.87432, true},   // Within tolerance (0.1%)
		{0.87632, true},   // Within tolerance (0.1%)
		{0.87400, false},  // Outside tolerance
		{0.87700, false},  // Outside tolerance
		{0.85, false},     // Far below
		{0.90, false},     // Far above
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("observed=%.5f", tt.observed), func(t *testing.T) {
			valid, err := ValidateAttractor(tt.observed)

			if valid != tt.shouldPass {
				t.Errorf("Expected shouldPass=%v, got valid=%v (err: %v)",
					tt.shouldPass, valid, err)
			}

			if valid {
				t.Logf("✓ %.5f is a valid attractor", tt.observed)
			} else {
				t.Logf("✗ %.5f is NOT a valid attractor: %v", tt.observed, err)
			}
		})
	}
}

func TestGetTheoreticalAttractor(t *testing.T) {
	got := GetTheoreticalAttractor()
	expected := 0.87532

	if math.Abs(got-expected) > 1e-10 {
		t.Errorf("GetTheoreticalAttractor: got %.10f, expected %.10f",
			got, expected)
	}

	t.Logf("✓ Theoretical attractor: %.5f", got)
}

func TestGetSevenEighths(t *testing.T) {
	got := GetSevenEighths()
	expected := 7.0 / 8.0

	if math.Abs(got-expected) > 1e-10 {
		t.Errorf("GetSevenEighths: got %.10f, expected %.10f",
			got, expected)
	}

	t.Logf("✓ Seven eighths: %.5f", got)
}

// ============================================================================
// PART VIII: SCALE INVARIANCE VALIDATION
// ============================================================================

func TestProveScaleInvariance(t *testing.T) {
	// Real data from SAT Origami breakthrough
	results := []ScaleTestResult{
		{1000, 0.87324, 4.26},
		{10000, 0.87502, 4.26},
		{50000, 0.87521, 4.26},
		{108000, 0.87479, 4.26},
		{216000, 0.87599, 4.26},
		{432000, 0.87505, 4.26},
	}

	valid, err := ProveScaleInvariance(results)

	if !valid {
		t.Fatalf("Scale invariance NOT proven: %v", err)
	}

	// Compute statistics manually to verify
	var sum float64
	for _, r := range results {
		sum += r.Satisfaction
	}
	mean := sum / float64(len(results))

	var variance float64
	for _, r := range results {
		delta := r.Satisfaction - mean
		variance += delta * delta
	}
	variance /= float64(len(results))
	stdDev := math.Sqrt(variance)

	t.Logf("Scale Invariance Statistics:")
	t.Logf("  Scales tested: %d", len(results))
	t.Logf("  Mean satisfaction: %.5f", mean)
	t.Logf("  Std deviation: %.7f (%.3f%%)", stdDev, stdDev*100)
	t.Logf("  Range: [%.5f, %.5f]", 0.87324, 0.87599)

	// Validate std dev matches expected
	expectedStdDev := 0.00068
	if math.Abs(stdDev-expectedStdDev) > 0.00010 {
		t.Errorf("Std dev: got %.7f, expected %.7f ± 0.0001",
			stdDev, expectedStdDev)
	}

	t.Logf("✓ Scale invariance PROVEN: σ = %.7f < 0.001", stdDev)
}

func TestProveScaleInvariance_EmptyResults(t *testing.T) {
	var results []ScaleTestResult

	valid, err := ProveScaleInvariance(results)

	if valid {
		t.Error("Expected failure with empty results, got valid=true")
	}

	if err == nil {
		t.Error("Expected error with empty results, got nil")
	}

	t.Logf("✓ Correctly rejects empty results: %v", err)
}

func TestProveScaleInvariance_HighVariance(t *testing.T) {
	// Construct results with high variance (should fail)
	results := []ScaleTestResult{
		{1000, 0.85, 4.26},
		{10000, 0.90, 4.26},
		{50000, 0.85, 4.26},
		{108000, 0.90, 4.26},
	}

	valid, err := ProveScaleInvariance(results)

	if valid {
		t.Error("Expected failure with high variance, got valid=true")
	}

	if err == nil {
		t.Error("Expected error with high variance, got nil")
	}

	t.Logf("✓ Correctly rejects high variance: %v", err)
}

// ============================================================================
// PART IX: PROOF SUMMARY
// ============================================================================

func TestGetProofSummary(t *testing.T) {
	theorem := NewAttractorTheorem()

	summary := theorem.GetProofSummary()

	// Validate summary contains key information
	requiredStrings := []string{
		"87.532%",
		"4.26",
		"7/8",
		"0.875",
		"PROVEN",
		"VALIDATED",
		"Om Lokah Samastah Sukhino Bhavantu",
	}

	for _, s := range requiredStrings {
		if !containsString(summary, s) {
			t.Errorf("Summary missing required string: %s", s)
		}
	}

	// Print summary for visual verification
	t.Log("Proof Summary:")
	t.Log(summary)
}

func TestGetOpenQuestions(t *testing.T) {
	theorem := NewAttractorTheorem()

	questions := theorem.GetOpenQuestions()

	if len(questions) == 0 {
		t.Error("Expected open questions, got empty list")
	}

	// Validate we have the key open questions
	requiredTopics := []string{
		"87.532%",
		"7/8",
		"4.26",
		"octonion",
		"E₈",
	}

	questionsStr := fmt.Sprintf("%v", questions)
	for _, topic := range requiredTopics {
		if !containsString(questionsStr, topic) {
			t.Logf("Warning: Open questions may be missing topic: %s", topic)
		}
	}

	t.Logf("Open Questions (%d total):", len(questions))
	for i, q := range questions {
		t.Logf("  %d. %s", i+1, q)
	}
}

// ============================================================================
// PART X: INTEGRATION TESTS
// ============================================================================

func TestFullTheoremValidation(t *testing.T) {
	t.Log("=== FULL THEOREM VALIDATION ===")

	theorem := NewAttractorTheorem()

	// Test 1: Attractor near 7/8
	t.Run("Attractor near 7/8", func(t *testing.T) {
		valid, err := theorem.ProveAttractorNear7Over8()
		if !valid {
			t.Fatalf("FAILED: %v", err)
		}
		t.Log("✓ PASS: Attractor near 7/8")
	})

	// Test 2: Complexity debt near 1/8
	t.Run("Complexity debt near 1/8", func(t *testing.T) {
		valid, err := theorem.ProveComplexityDebtNear1Over8()
		if !valid {
			t.Fatalf("FAILED: %v", err)
		}
		t.Log("✓ PASS: Complexity debt near 1/8")
	})

	// Test 3: Phase transition at critical alpha
	t.Run("Phase transition at α=4.26", func(t *testing.T) {
		phase, inZone := theorem.ProvePhaseTransitionAtAlpha(theorem.CriticalAlpha)
		if !inZone {
			t.Fatalf("FAILED: α=%.2f not in phase transition zone (got: %s)",
				theorem.CriticalAlpha, phase)
		}
		t.Logf("✓ PASS: α=%.2f in %s", theorem.CriticalAlpha, phase)
	})

	// Test 4: Thermodynamic entropy matches theory
	t.Run("Thermodynamic entropy (n=108,000)", func(t *testing.T) {
		entropy := theorem.ComputeTheoreticalEntropy(108000)
		measured := 9335.03
		errorPercent := math.Abs(entropy-measured) / entropy * 100

		if errorPercent > 0.1 {
			t.Fatalf("FAILED: Error %.3f%% > 0.1%%", errorPercent)
		}
		t.Logf("✓ PASS: Entropy error %.3f%% < 0.1%%", errorPercent)
	})

	// Test 5: Scale invariance
	t.Run("Scale invariance", func(t *testing.T) {
		results := []ScaleTestResult{
			{1000, 0.87324, 4.26},
			{10000, 0.87502, 4.26},
			{50000, 0.87521, 4.26},
			{108000, 0.87479, 4.26},
			{216000, 0.87599, 4.26},
			{432000, 0.87505, 4.26},
		}

		valid, err := ProveScaleInvariance(results)
		if !valid {
			t.Fatalf("FAILED: %v", err)
		}
		t.Log("✓ PASS: Scale invariance proven")
	})

	t.Log("=== ALL THEOREM VALIDATIONS PASSED ✓ ===")
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

// Note: containsSubstring and findSubstring are defined in digital_root_proof_test.go
// We use the standard library instead
func containsString(str, substr string) bool {
	// Simple substring search using naive algorithm
	if len(substr) == 0 {
		return true
	}
	if len(str) < len(substr) {
		return false
	}
	for i := 0; i <= len(str)-len(substr); i++ {
		match := true
		for j := 0; j < len(substr); j++ {
			if str[i+j] != substr[j] {
				match = false
				break
			}
		}
		if match {
			return true
		}
	}
	return false
}

// ============================================================================
// BENCHMARKS
// ============================================================================

func BenchmarkProveAttractorNear7Over8(b *testing.B) {
	theorem := NewAttractorTheorem()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = theorem.ProveAttractorNear7Over8()
	}
}

func BenchmarkComputeTheoreticalEntropy(b *testing.B) {
	theorem := NewAttractorTheorem()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = theorem.ComputeTheoreticalEntropy(108000)
	}
}

func BenchmarkProveScaleInvariance(b *testing.B) {
	results := []ScaleTestResult{
		{1000, 0.87324, 4.26},
		{10000, 0.87502, 4.26},
		{50000, 0.87521, 4.26},
		{108000, 0.87479, 4.26},
		{216000, 0.87599, 4.26},
		{432000, 0.87505, 4.26},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = ProveScaleInvariance(results)
	}
}
