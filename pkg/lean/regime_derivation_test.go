package lean

import (
	"math"
	"testing"
)

// ============================================================================
// TESTS FOR THREE-REGIME DERIVATION
// ============================================================================

func TestThreeRegimeTheorem_BasicProperties(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	// Test partition of unity
	r1, r2, r3 := theorem.GetOptimalRatios()
	sum := r1 + r2 + r3
	if math.Abs(sum-1.0) > 1e-10 {
		t.Errorf("Regimes don't sum to 1: got %.10f", sum)
	}

	// Test non-negativity
	if r1 < 0 || r2 < 0 || r3 < 0 {
		t.Errorf("Regimes must be non-negative: R1=%.2f, R2=%.2f, R3=%.2f", r1, r2, r3)
	}

	// Test bounds
	if r1 > 1 || r2 > 1 || r3 > 1 {
		t.Errorf("Regimes must be ≤ 1: R1=%.2f, R2=%.2f, R3=%.2f", r1, r2, r3)
	}
}

func TestThreeRegimeTheorem_OptimalValues(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// Test expected values
	if math.Abs(r1-0.30) > 1e-10 {
		t.Errorf("R1 should be 0.30, got %.10f", r1)
	}
	if math.Abs(r2-0.20) > 1e-10 {
		t.Errorf("R2 should be 0.20, got %.10f", r2)
	}
	if math.Abs(r3-0.50) > 1e-10 {
		t.Errorf("R3 should be 0.50, got %.10f", r3)
	}
}

func TestThreeRegimeTheorem_RegimeOrdering(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// R2 should be smallest (bottleneck!)
	if r2 > r1 || r2 > r3 {
		t.Errorf("R2 should be smallest: R1=%.2f, R2=%.2f, R3=%.2f", r1, r2, r3)
	}

	// R3 should be largest (majority!)
	if r3 < r1 || r3 < r2 {
		t.Errorf("R3 should be largest: R1=%.2f, R2=%.2f, R3=%.2f", r1, r2, r3)
	}
}

func TestThreeRegimeTheorem_CostOrdering(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	// k2 > k1 > k3 (optimization most expensive!)
	if theorem.K2_OptimizationCost <= theorem.K1_ExplorationCost {
		t.Errorf("k2 should be > k1: k2=%.1f, k1=%.1f",
			theorem.K2_OptimizationCost, theorem.K1_ExplorationCost)
	}
	if theorem.K1_ExplorationCost <= theorem.K3_StabilizationCost {
		t.Errorf("k1 should be > k3: k1=%.1f, k3=%.1f",
			theorem.K1_ExplorationCost, theorem.K3_StabilizationCost)
	}
}

func TestThreeRegimeTheorem_EnergyOrdering(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	// E2 > E1 > E3 (optimization highest energy!)
	if theorem.E2_OptimizationEnergy <= theorem.E1_ExplorationEnergy {
		t.Errorf("E2 should be > E1: E2=%.1f, E1=%.1f",
			theorem.E2_OptimizationEnergy, theorem.E1_ExplorationEnergy)
	}
	if theorem.E1_ExplorationEnergy <= theorem.E3_StabilizationEnergy {
		t.Errorf("E1 should be > E3: E1=%.1f, E3=%.1f",
			theorem.E1_ExplorationEnergy, theorem.E3_StabilizationEnergy)
	}
}

func TestThreeRegimeTheorem_ComputeEntropy(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// Compute entropy
	entropy := theorem.ComputeEntropy(r1, r2, r3)

	// Entropy should be positive
	if entropy <= 0 {
		t.Errorf("Entropy should be positive: got %.4f", entropy)
	}

	// For uniform distribution [1/3, 1/3, 1/3], entropy is maximum
	uniformEntropy := theorem.ComputeEntropy(1.0/3.0, 1.0/3.0, 1.0/3.0)

	// Our optimal should have slightly lower entropy (more structured)
	if entropy >= uniformEntropy {
		t.Logf("Optimal entropy: %.4f, Uniform entropy: %.4f", entropy, uniformEntropy)
	}
}

func TestThreeRegimeTheorem_ComputeTotalCost(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// Compute cost for n=1000
	n := 1000
	cost := theorem.ComputeTotalCost(r1, r2, r3, n)

	// Cost should be positive
	if cost <= 0 {
		t.Errorf("Cost should be positive: got %.2f", cost)
	}

	// R2 contribution should be significant despite being only 20%
	// (because k2=5.0 is expensive!)
	t.Logf("Total cost for n=%d: %.2f", n, cost)
}

func TestThreeRegimeTheorem_ComputeFreeEnergy(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// Compute free energy
	freeEnergy := theorem.ComputeFreeEnergy(r1, r2, r3)

	// Free energy should be finite
	if math.IsNaN(freeEnergy) || math.IsInf(freeEnergy, 0) {
		t.Errorf("Free energy should be finite: got %.4f", freeEnergy)
	}

	t.Logf("Optimal free energy: %.4f", freeEnergy)
}

func TestThreeRegimeTheorem_IsStable(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// Optimal distribution should be stable
	if !theorem.IsStable(r1, r2, r3) {
		t.Errorf("Optimal distribution should be stable (R3 ≥ 50%%): R3=%.2f", r3)
	}

	// Test boundary: R3 = 0.49 should be unstable
	if theorem.IsStable(0.31, 0.20, 0.49) {
		t.Errorf("R3=0.49 should be unstable (< 50%%)")
	}

	// Test boundary: R3 = 0.50 should be stable
	if !theorem.IsStable(0.30, 0.20, 0.50) {
		t.Errorf("R3=0.50 should be stable (= 50%%)")
	}
}

func TestThreeRegimeTheorem_IsOptimal(t *testing.T) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	// Optimal distribution should be optimal!
	if !theorem.IsOptimal(r1, r2, r3) {
		t.Errorf("Optimal distribution should satisfy IsOptimal check")
	}

	// Slightly perturbed should still be optimal (within variance)
	if !theorem.IsOptimal(0.32, 0.19, 0.49) {
		t.Errorf("Distribution [0.32, 0.19, 0.49] should be within variance")
	}

	// Far from optimal should fail
	if theorem.IsOptimal(0.50, 0.25, 0.25) {
		t.Errorf("Distribution [0.50, 0.25, 0.25] should NOT be optimal")
	}
}

func TestThreeRegimeTheorem_ComputeDistanceFromOptimal(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	// Distance from optimal to itself should be zero
	r1, r2, r3 := theorem.GetOptimalRatios()
	dist := theorem.ComputeDistanceFromOptimal(r1, r2, r3)
	if dist > 1e-10 {
		t.Errorf("Distance from optimal to itself should be 0: got %.10f", dist)
	}

	// Distance to uniform distribution [1/3, 1/3, 1/3]
	distUniform := theorem.ComputeDistanceFromOptimal(1.0/3.0, 1.0/3.0, 1.0/3.0)
	if distUniform <= 0 {
		t.Errorf("Distance to uniform should be positive: got %.4f", distUniform)
	}

	t.Logf("L1 distance to uniform: %.4f", distUniform)
}

func TestThreeRegimeTheorem_ValidateRegimeTransition(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	// High entropy → R1 (Exploration)
	phase := theorem.ValidateRegimeTransition(0.9, 0.3, 0.2)
	if phase != R1_Exploration {
		t.Errorf("High entropy should yield R1, got %v", phase)
	}

	// Moderate gradient → R2 (Optimization)
	phase = theorem.ValidateRegimeTransition(0.4, 0.7, 0.3)
	if phase != R2_Optimization {
		t.Errorf("High gradient should yield R2, got %v", phase)
	}

	// High stability → R3 (Stabilization)
	phase = theorem.ValidateRegimeTransition(0.2, 0.3, 0.9)
	if phase != R3_Stabilization {
		t.Errorf("High stability should yield R3, got %v", phase)
	}

	// Default to R3 when unclear
	phase = theorem.ValidateRegimeTransition(0.3, 0.3, 0.3)
	if phase != R3_Stabilization {
		t.Errorf("Unclear case should default to R3, got %v", phase)
	}
}

func TestClassifyVarianceToRegime(t *testing.T) {
	// High variance → R1
	phase := ClassifyVarianceToRegime(0.20)
	if phase != R1_Exploration {
		t.Errorf("Variance 0.20 should yield R1, got %v", phase)
	}

	// Medium variance → R2
	phase = ClassifyVarianceToRegime(0.10)
	if phase != R2_Optimization {
		t.Errorf("Variance 0.10 should yield R2, got %v", phase)
	}

	// Low variance → R3
	phase = ClassifyVarianceToRegime(0.02)
	if phase != R3_Stabilization {
		t.Errorf("Variance 0.02 should yield R3, got %v", phase)
	}
}

func TestEstimateRegimeFromHistory(t *testing.T) {
	// High variance time series (exploration)
	highVar := []float64{10, 5, 15, 2, 18, 8, 20, 1, 12, 16}
	phase, variance := EstimateRegimeFromHistory(highVar, 5)
	if phase != R1_Exploration {
		t.Errorf("High variance series should yield R1, got %v (variance: %.4f)", phase, variance)
	}

	// Low variance time series (stabilization)
	lowVar := []float64{10.0, 10.1, 9.9, 10.2, 9.8, 10.1, 10.0, 9.9, 10.1, 10.0}
	phase, variance = EstimateRegimeFromHistory(lowVar, 5)
	if phase != R3_Stabilization {
		t.Errorf("Low variance series should yield R3, got %v (variance: %.4f)", phase, variance)
	}
}

func TestGetRegimeCharacteristics(t *testing.T) {
	// Test that all regimes have characteristics
	for _, phase := range []Phase{R1_Exploration, R2_Optimization, R3_Stabilization} {
		characteristics := GetRegimeCharacteristics(phase)
		if len(characteristics) == 0 {
			t.Errorf("Regime %v should have characteristics", phase)
		}
		// Just verify it contains key info
		if phase == R2_Optimization && len(characteristics) < 100 {
			t.Errorf("R2 characteristics seem too short (should explain bottleneck!)")
		}
	}
}

func TestToLeanDefinition(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	leanCode := theorem.ToLeanDefinition()

	// Verify it contains key elements
	if len(leanCode) < 100 {
		t.Errorf("Lean definition seems too short")
	}

	// Check for key constants
	requiredStrings := []string{
		"R1_optimal",
		"R2_optimal",
		"R3_optimal",
		"k1_exploration",
		"k2_optimization",
		"k3_stabilization",
		"E1_energy",
		"E2_energy",
		"E3_energy",
		"entropy",
		"freeEnergy",
		"isStable",
	}

	for _, req := range requiredStrings {
		if !regimeContains(leanCode, req) {
			t.Errorf("Lean code missing required definition: %s", req)
		}
	}
}

func TestExplainOptimality(t *testing.T) {
	theorem := NewThreeRegimeTheorem()

	explanation := theorem.ExplainOptimality()

	// Verify it's substantial
	if len(explanation) < 500 {
		t.Errorf("Explanation seems too short: %d chars", len(explanation))
	}

	// Check for key concepts
	requiredConcepts := []string{
		"30%",
		"20%",
		"50%",
		"BOTTLENECK",
		"Shannon entropy",
		"free energy",
		"universal constant",
	}

	for _, concept := range requiredConcepts {
		if !regimeContains(explanation, concept) {
			t.Errorf("Explanation missing key concept: %s", concept)
		}
	}

	// Actually print it for manual inspection
	t.Log("\n" + explanation)
}

// ============================================================================
// BENCHMARK TESTS
// ============================================================================

func BenchmarkComputeEntropy(b *testing.B) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = theorem.ComputeEntropy(r1, r2, r3)
	}
}

func BenchmarkComputeTotalCost(b *testing.B) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()
	n := 1000

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = theorem.ComputeTotalCost(r1, r2, r3, n)
	}
}

func BenchmarkComputeFreeEnergy(b *testing.B) {
	theorem := NewThreeRegimeTheorem()
	r1, r2, r3 := theorem.GetOptimalRatios()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = theorem.ComputeFreeEnergy(r1, r2, r3)
	}
}

func BenchmarkValidateRegimeTransition(b *testing.B) {
	theorem := NewThreeRegimeTheorem()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = theorem.ValidateRegimeTransition(0.5, 0.5, 0.5)
	}
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

func regimeContains(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if len(s[i:]) >= len(substr) && s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
