// Package intelligence - SHM Calculator Exhaustive Tests
//
// Mathematical Foundation (from research paper):
//   Formula: SHM = Σ (sonar_score × weight) / Σ weights
//   Weights: { UX: 0.25, Design: 0.25, Code: 0.125, Semantic: 0.125, Journey: 0.125, State: 0.125 }
//   Regime Boundaries:
//     - SHM < 0.70 → Exploration
//     - 0.70 ≤ SHM < 0.85 → Optimization
//     - SHM ≥ 0.85 → Stabilization
//
// Author: Wave 1 Agent 4 (EXHAUSTIVE test coverage!)
// Created: 2025-12-27
package intelligence

import (
	"math"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// STABILIZATION TESTS (100% Required) - Weights Validation
// ═══════════════════════════════════════════════════════════════════════════

// TestSHMWeights_SumToOne validates that all weights sum to exactly 1.0
//
// Formula: Σ weights = 1.0
// Mathematical requirement: weighted average must preserve scale
func TestSHMWeights_SumToOne(t *testing.T) {
	shm := NewSHMCalculator()

	sum := 0.0
	for _, weight := range shm.weights {
		sum += weight
	}

	// Exact validation (critical for mathematical correctness!)
	if sum != 1.0 {
		t.Errorf("Weights sum = %.10f, want exactly 1.0", sum)
	}

	t.Logf("✅ Weights sum to 1.0 (verified: %.10f)", sum)
}

// TestSHMWeights_UX validates UX weight is exactly 0.25
//
// From research paper: UX is 25% of total weight (user-facing priority)
func TestSHMWeights_UX(t *testing.T) {
	shm := NewSHMCalculator()

	expected := 0.25
	actual := shm.weights["ux"]

	if actual != expected {
		t.Errorf("UX weight = %.10f, want %.10f", actual, expected)
	}

	t.Logf("✅ UX weight = %.2f (25%% user-facing)", actual)
}

// TestSHMWeights_Design validates Design weight is exactly 0.25
//
// From research paper: Design is 25% of total weight (user-facing priority)
func TestSHMWeights_Design(t *testing.T) {
	shm := NewSHMCalculator()

	expected := 0.25
	actual := shm.weights["design"]

	if actual != expected {
		t.Errorf("Design weight = %.10f, want %.10f", actual, expected)
	}

	t.Logf("✅ Design weight = %.2f (25%% user-facing)", actual)
}

// TestSHMWeights_Code validates Code weight is exactly 0.125
//
// From research paper: Code is 12.5% of total weight (internal quality)
func TestSHMWeights_Code(t *testing.T) {
	shm := NewSHMCalculator()

	expected := 0.125
	actual := shm.weights["code"]

	if actual != expected {
		t.Errorf("Code weight = %.10f, want %.10f", actual, expected)
	}

	t.Logf("✅ Code weight = %.3f (12.5%% internal quality)", actual)
}

// TestSHMWeights_Semantic validates Semantic weight is exactly 0.125
//
// From research paper: Semantic is 12.5% of total weight (internal quality)
func TestSHMWeights_Semantic(t *testing.T) {
	shm := NewSHMCalculator()

	expected := 0.125
	actual := shm.weights["semantic"]

	if actual != expected {
		t.Errorf("Semantic weight = %.10f, want %.10f", actual, expected)
	}

	t.Logf("✅ Semantic weight = %.3f (12.5%% internal quality)", actual)
}

// TestSHMWeights_Journey validates Journey weight is exactly 0.125
//
// From research paper: Journey is 12.5% of total weight (internal quality)
func TestSHMWeights_Journey(t *testing.T) {
	shm := NewSHMCalculator()

	expected := 0.125
	actual := shm.weights["journey"]

	if actual != expected {
		t.Errorf("Journey weight = %.10f, want %.10f", actual, expected)
	}

	t.Logf("✅ Journey weight = %.3f (12.5%% internal quality)", actual)
}

// TestSHMWeights_State validates State weight is exactly 0.125
//
// From research paper: State is 12.5% of total weight (internal quality)
func TestSHMWeights_State(t *testing.T) {
	shm := NewSHMCalculator()

	expected := 0.125
	actual := shm.weights["state"]

	if actual != expected {
		t.Errorf("State weight = %.10f, want %.10f", actual, expected)
	}

	t.Logf("✅ State weight = %.3f (12.5%% internal quality)", actual)
}

// TestSHMCalculation_AllPerfect validates SHM with all perfect scores
//
// Formula: SHM = Σ(1.0 × weight) / Σ(weights) = 1.0
func TestSHMCalculation_AllPerfect(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       1.0,
		"design":   1.0,
		"code":     1.0,
		"semantic": 1.0,
		"journey":  1.0,
		"state":    1.0,
	}

	result := shm.computeWeightedSHM(scores)

	// All perfect scores MUST yield SHM = 1.0
	if result != 1.0 {
		t.Errorf("SHM with all 1.0 scores = %.10f, want exactly 1.0", result)
	}

	t.Logf("✅ All perfect scores → SHM = %.1f", result)
}

// TestSHMCalculation_AllZero validates SHM with all zero scores
//
// Formula: SHM = Σ(0.0 × weight) / Σ(weights) = 0.0
func TestSHMCalculation_AllZero(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       0.0,
		"design":   0.0,
		"code":     0.0,
		"semantic": 0.0,
		"journey":  0.0,
		"state":    0.0,
	}

	result := shm.computeWeightedSHM(scores)

	// All zero scores MUST yield SHM = 0.0
	if result != 0.0 {
		t.Errorf("SHM with all 0.0 scores = %.10f, want exactly 0.0", result)
	}

	t.Logf("✅ All zero scores → SHM = %.1f", result)
}

// TestSHMCalculation_Mixed validates SHM with realistic mixed scores
//
// Formula: SHM = (0.90×0.25 + 0.85×0.25 + 0.75×0.125 + 0.80×0.125 + 0.95×0.125 + 0.70×0.125)
//        = 0.225 + 0.2125 + 0.09375 + 0.10 + 0.11875 + 0.0875
//        = 0.8375
func TestSHMCalculation_Mixed(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       0.90,
		"design":   0.85,
		"code":     0.75,
		"semantic": 0.80,
		"journey":  0.95,
		"state":    0.70,
	}

	result := shm.computeWeightedSHM(scores)

	// Hand-calculated expected value
	expected := 0.8375
	tolerance := 0.0001

	if result < expected-tolerance || result > expected+tolerance {
		t.Errorf("SHM with mixed scores = %.10f, want %.10f (±%.4f)",
			result, expected, tolerance)
	}

	t.Logf("✅ Mixed scores → SHM = %.4f (expected: %.4f)", result, expected)
}

// ═══════════════════════════════════════════════════════════════════════════
// STABILIZATION TESTS (100% Required) - Regime Determination
// ═══════════════════════════════════════════════════════════════════════════

// TestRegimeDetermination_Exploration validates boundary: SHM < 0.70
//
// Regime Rule: SHM < 0.70 → EXPLORATION
func TestRegimeDetermination_Exploration(t *testing.T) {
	shm := NewSHMCalculator()

	tests := []struct {
		name     string
		shmValue float64
	}{
		{"Zero (0.00)", 0.00},
		{"Very low (0.20)", 0.20},
		{"Low (0.50)", 0.50},
		{"Just below boundary (0.69)", 0.69},
		{"Exact boundary (0.699999)", 0.699999},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			regime := shm.determineRegime(tt.shmValue)

			if regime != RegimeExploration {
				t.Errorf("SHM %.6f → %s, want %s",
					tt.shmValue, regime, RegimeExploration)
			}

			t.Logf("✅ SHM %.6f → EXPLORATION", tt.shmValue)
		})
	}
}

// TestRegimeDetermination_Optimization validates boundary: 0.70 ≤ SHM < 0.85
//
// Regime Rule: 0.70 ≤ SHM < 0.85 → OPTIMIZATION
func TestRegimeDetermination_Optimization(t *testing.T) {
	shm := NewSHMCalculator()

	tests := []struct {
		name     string
		shmValue float64
	}{
		{"Lower boundary (0.70)", 0.70},
		{"Just above lower (0.700001)", 0.700001},
		{"Middle (0.75)", 0.75},
		{"Middle-high (0.80)", 0.80},
		{"Just below upper (0.84)", 0.84},
		{"Upper boundary (0.849999)", 0.849999},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			regime := shm.determineRegime(tt.shmValue)

			if regime != RegimeOptimization {
				t.Errorf("SHM %.6f → %s, want %s",
					tt.shmValue, regime, RegimeOptimization)
			}

			t.Logf("✅ SHM %.6f → OPTIMIZATION", tt.shmValue)
		})
	}
}

// TestRegimeDetermination_Stabilization validates boundary: SHM ≥ 0.85
//
// Regime Rule: SHM ≥ 0.85 → STABILIZATION
func TestRegimeDetermination_Stabilization(t *testing.T) {
	shm := NewSHMCalculator()

	tests := []struct {
		name     string
		shmValue float64
	}{
		{"Lower boundary (0.85)", 0.85},
		{"Just above lower (0.850001)", 0.850001},
		{"High (0.90)", 0.90},
		{"Very high (0.95)", 0.95},
		{"Perfect (1.00)", 1.00},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			regime := shm.determineRegime(tt.shmValue)

			if regime != RegimeStabilization {
				t.Errorf("SHM %.6f → %s, want %s",
					tt.shmValue, regime, RegimeStabilization)
			}

			t.Logf("✅ SHM %.6f → STABILIZATION", tt.shmValue)
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// OPTIMIZATION TESTS (85% Required) - Advanced Calculations
// ═══════════════════════════════════════════════════════════════════════════

// TestSHMCalculation_UserFacingDominance validates UX+Design = 50% weight
//
// From research paper: User-facing dimensions (UX + Design) get 50% of total weight
// Internal quality dimensions (Code + Semantic + Journey + State) get 50% of total weight
func TestSHMCalculation_UserFacingDominance(t *testing.T) {
	shm := NewSHMCalculator()

	// Test 1: Perfect user-facing, zero internal
	scores1 := map[string]float64{
		"ux":       1.0,
		"design":   1.0,
		"code":     0.0,
		"semantic": 0.0,
		"journey":  0.0,
		"state":    0.0,
	}

	result1 := shm.computeWeightedSHM(scores1)
	expected1 := 0.50 // Should contribute exactly 50%

	if result1 != expected1 {
		t.Errorf("Perfect user-facing only: SHM = %.4f, want %.2f", result1, expected1)
	}

	t.Logf("✅ Perfect user-facing (UX + Design = 1.0) → SHM = %.2f (50%% contribution)", result1)

	// Test 2: Zero user-facing, perfect internal
	scores2 := map[string]float64{
		"ux":       0.0,
		"design":   0.0,
		"code":     1.0,
		"semantic": 1.0,
		"journey":  1.0,
		"state":    1.0,
	}

	result2 := shm.computeWeightedSHM(scores2)
	expected2 := 0.50 // Should contribute exactly 50%

	if result2 != expected2 {
		t.Errorf("Perfect internal only: SHM = %.4f, want %.2f", result2, expected2)
	}

	t.Logf("✅ Perfect internal (Code + Semantic + Journey + State = 1.0) → SHM = %.2f (50%% contribution)", result2)
}

// TestSHMCalculation_WeightedInfluence validates that weights properly influence result
//
// Test: UX should influence SHM 2× more than Code (0.25 vs 0.125)
func TestSHMCalculation_WeightedInfluence(t *testing.T) {
	shm := NewSHMCalculator()

	// Test 1: Only UX is perfect
	scoresUX := map[string]float64{
		"ux":       1.0,
		"design":   0.0,
		"code":     0.0,
		"semantic": 0.0,
		"journey":  0.0,
		"state":    0.0,
	}

	resultUX := shm.computeWeightedSHM(scoresUX)

	// Test 2: Only Code is perfect
	scoresCode := map[string]float64{
		"ux":       0.0,
		"design":   0.0,
		"code":     1.0,
		"semantic": 0.0,
		"journey":  0.0,
		"state":    0.0,
	}

	resultCode := shm.computeWeightedSHM(scoresCode)

	// Verify: UX contribution (0.25) should be 2× Code contribution (0.125)
	ratio := resultUX / resultCode
	expectedRatio := 2.0
	tolerance := 0.01

	if ratio < expectedRatio-tolerance || ratio > expectedRatio+tolerance {
		t.Errorf("UX/Code influence ratio = %.4f, want %.2f (±%.2f)",
			ratio, expectedRatio, tolerance)
	}

	t.Logf("✅ UX influence (%.2f) is 2× Code influence (%.3f) [ratio: %.2f]",
		resultUX, resultCode, ratio)
}

// TestSHMCalculation_BoundaryPrecision validates exact regime boundaries
//
// Critical boundaries: 0.70 and 0.85 must be precise!
func TestSHMCalculation_BoundaryPrecision(t *testing.T) {
	shm := NewSHMCalculator()

	tests := []struct {
		name          string
		targetSHM     float64
		expectedRegime Regime
	}{
		{"Just below 0.70 (0.6999)", 0.6999, RegimeExploration},
		{"Exactly 0.70", 0.70, RegimeOptimization},
		{"Just above 0.70 (0.7001)", 0.7001, RegimeOptimization},
		{"Just below 0.85 (0.8499)", 0.8499, RegimeOptimization},
		{"Exactly 0.85", 0.85, RegimeStabilization},
		{"Just above 0.85 (0.8501)", 0.8501, RegimeStabilization},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			regime := shm.determineRegime(tt.targetSHM)

			if regime != tt.expectedRegime {
				t.Errorf("SHM %.4f → %s, want %s",
					tt.targetSHM, regime, tt.expectedRegime)
			}

			t.Logf("✅ SHM %.4f → %s (boundary precision verified)", tt.targetSHM, regime)
		})
	}
}

// TestSHMCalculation_SymmetricScores validates symmetry in weighted averaging
//
// Mathematical property: swapping scores with same weight should not change SHM
func TestSHMCalculation_SymmetricScores(t *testing.T) {
	shm := NewSHMCalculator()

	// Test 1: Swap UX and Design (both 0.25)
	scores1 := map[string]float64{
		"ux":       0.90,
		"design":   0.80,
		"code":     0.75,
		"semantic": 0.75,
		"journey":  0.75,
		"state":    0.75,
	}

	scores2 := map[string]float64{
		"ux":       0.80,
		"design":   0.90,
		"code":     0.75,
		"semantic": 0.75,
		"journey":  0.75,
		"state":    0.75,
	}

	result1 := shm.computeWeightedSHM(scores1)
	result2 := shm.computeWeightedSHM(scores2)

	if result1 != result2 {
		t.Errorf("Swapping UX/Design changed SHM: %.4f vs %.4f", result1, result2)
	}

	t.Logf("✅ Swapping UX (0.90) ↔ Design (0.80): SHM unchanged = %.4f", result1)

	// Test 2: Swap internal quality scores (all 0.125)
	scores3 := map[string]float64{
		"ux":       0.85,
		"design":   0.85,
		"code":     0.70,
		"semantic": 0.80,
		"journey":  0.90,
		"state":    0.60,
	}

	scores4 := map[string]float64{
		"ux":       0.85,
		"design":   0.85,
		"code":     0.90,
		"semantic": 0.60,
		"journey":  0.80,
		"state":    0.70,
	}

	result3 := shm.computeWeightedSHM(scores3)
	result4 := shm.computeWeightedSHM(scores4)

	// Allow small floating point tolerance
	tolerance := 0.0001
	if math.Abs(result3-result4) > tolerance {
		t.Errorf("Swapping internal quality scores changed SHM: %.4f vs %.4f", result3, result4)
	}

	t.Logf("✅ Swapping internal quality scores: SHM unchanged = %.4f", result3)
}

// ═══════════════════════════════════════════════════════════════════════════
// EXPLORATION TESTS (70% Required) - Edge Cases
// ═══════════════════════════════════════════════════════════════════════════

// TestSHMCalculation_EmptyWeights validates behavior with empty weights (edge case)
//
// Expected: Return 0.0 if no weights (avoid division by zero)
func TestSHMCalculation_EmptyWeights(t *testing.T) {
	shm := &SHMCalculator{
		weights: make(map[string]float64), // Empty weights
	}

	scores := map[string]float64{
		"ux": 1.0,
	}

	result := shm.computeWeightedSHM(scores)

	// Should return 0.0 to avoid division by zero
	if result != 0.0 {
		t.Errorf("SHM with empty weights = %.4f, want 0.0", result)
	}

	t.Logf("✅ Empty weights → SHM = %.1f (division by zero avoided)", result)
}

// TestSHMCalculation_NegativeScores validates behavior with negative scores (invalid input)
//
// Edge case: What happens if a sonar returns negative score?
func TestSHMCalculation_NegativeScores(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       -0.50, // Invalid!
		"design":   0.90,
		"code":     0.80,
		"semantic": 0.80,
		"journey":  0.80,
		"state":    0.80,
	}

	result := shm.computeWeightedSHM(scores)

	// Calculation still proceeds, but result may be unexpected
	// This documents current behavior (could add validation later)
	t.Logf("⚠️  Negative score (-0.50) → SHM = %.4f (behavior documented)", result)

	// SHM should be less than max possible due to negative contribution
	if result >= 1.0 {
		t.Error("SHM with negative score should be < 1.0")
	}
}

// TestSHMCalculation_ScoresAboveOne validates behavior with scores > 1.0 (invalid input)
//
// Edge case: What happens if a sonar returns score > 1.0?
func TestSHMCalculation_ScoresAboveOne(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       1.50, // Invalid!
		"design":   0.90,
		"code":     0.80,
		"semantic": 0.80,
		"journey":  0.80,
		"state":    0.80,
	}

	result := shm.computeWeightedSHM(scores)

	// Calculation still proceeds
	// Expected: (1.50×0.25 + 0.90×0.25 + 0.80×0.125 + 0.80×0.125 + 0.80×0.125 + 0.80×0.125)
	//         = 0.375 + 0.225 + 0.100 + 0.100 + 0.100 + 0.100 = 1.00
	t.Logf("⚠️  Score > 1.0 (1.50) → SHM = %.4f (behavior documented)", result)

	// Current implementation allows scores > 1.0, result may or may not exceed 1.0
	// This documents current behavior (validation could be added later)
	if result < 0.0 {
		t.Error("SHM should be non-negative even with invalid inputs")
	}
}

// TestFindExtremes_SingleSonar validates extremes detection with single sonar
//
// Edge case: What if only one sonar has data?
func TestFindExtremes_SingleSonar(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux": 0.75,
	}

	weakest, strongest := shm.findExtremes(scores)

	// Both should be "ux" since it's the only one
	if weakest != "ux" || strongest != "ux" {
		t.Errorf("Single sonar: weakest=%s, strongest=%s, want both=ux",
			weakest, strongest)
	}

	t.Logf("✅ Single sonar: weakest=%s, strongest=%s (both same)", weakest, strongest)
}

// TestFindExtremes_AllEqual validates extremes detection with all equal scores
//
// Edge case: What if all scores are identical?
func TestFindExtremes_AllEqual(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       0.80,
		"design":   0.80,
		"code":     0.80,
		"semantic": 0.80,
		"journey":  0.80,
		"state":    0.80,
	}

	weakest, strongest := shm.findExtremes(scores)

	// Both should be the same sonar (which one is implementation-dependent)
	t.Logf("⚠️  All equal (0.80): weakest=%s, strongest=%s (implementation-dependent)",
		weakest, strongest)

	// Both should have score 0.80
	if scores[weakest] != 0.80 || scores[strongest] != 0.80 {
		t.Error("With all equal scores, both extremes should have score 0.80")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// REGRESSION TESTS - Prevent Past Bugs
// ═══════════════════════════════════════════════════════════════════════════

// TestSHMCalculation_KnownGoodValue validates against known good calculation
//
// Regression test: Ensures calculation matches reference implementation
func TestSHMCalculation_KnownGoodValue(t *testing.T) {
	shm := NewSHMCalculator()

	// Reference scores from existing test
	scores := map[string]float64{
		"ux":       0.90,
		"design":   0.85,
		"code":     0.75,
		"semantic": 0.80,
		"journey":  0.95,
		"state":    0.70,
	}

	result := shm.computeWeightedSHM(scores)

	// Reference value: 0.8375 (from original test)
	expected := 0.8375
	tolerance := 0.0001

	if result < expected-tolerance || result > expected+tolerance {
		t.Errorf("REGRESSION: SHM = %.10f, want %.10f (±%.4f)",
			result, expected, tolerance)
	}

	t.Logf("✅ Regression test: SHM = %.4f (matches reference)", result)
}
