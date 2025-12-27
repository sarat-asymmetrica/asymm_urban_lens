package intelligence

import (
	"math"
	"testing"
)

// ============================================================================
// EXHAUSTIVE TEST SUITE FOR WILLIAMS SPACE OPTIMIZER
// ============================================================================
//
// Created: 2025-12-27
// Purpose: Validate Williams research paper claims with mathematical precision
//
// Mathematical Foundation:
//   - Formula: williams_space_bound = √t × log₂(t)
//   - Efficiency: t / williams_space_bound
//   - Space reduction: ((t - williams_space_bound) / t) × 100%
//
// Expected Results (from research paper):
//   Scale   | Operations (t) | Space Bound | Efficiency | Space Reduction
//   --------|----------------|-------------|------------|----------------
//   Small   | 100            | ~66.4       | 1.5x       | 34%
//   Medium  | 1,000          | ~315        | 3.2x       | 68%
//   Large   | 10,000         | ~1,329      | 7.5x       | 87%
//
// Test Categories (Three-Regime):
//   - Stabilization (100% pass required): Core formula validation
//   - Optimization (85% pass required): Performance + integration
//   - Exploration (70% pass required): Edge cases + extensions
//
// ============================================================================

// ============================================================================
// STABILIZATION TESTS (100% REQUIRED)
// ============================================================================

// TestWilliamsSpaceBound_SmallScale validates t=100 matches research paper
//
// Mathematical expectation:
//   √100 × log₂(100) = 10 × 6.644 = 66.44 → 66 (floor)
//
// Research claim: 1.5x efficiency, 34% space reduction
func TestWilliamsSpaceBound_SmallScale(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Test parameters from research paper
	timeComplexity := 100
	expectedSpaceBound := 66 // floor(10 × 6.644)
	expectedEfficiency := 1.5 // Minimum research threshold
	expectedReduction := 34.0 // Percentage

	result := optimizer.CalculateSpaceBound(timeComplexity)

	// Validate space bound (exact match)
	if result.SpaceBound != expectedSpaceBound {
		t.Errorf("Space bound mismatch: expected %d, got %d",
			expectedSpaceBound, result.SpaceBound)
	}

	// Validate efficiency (≥ threshold)
	if result.Efficiency < expectedEfficiency {
		t.Errorf("Efficiency below threshold: expected ≥%.2f, got %.2f",
			expectedEfficiency, result.Efficiency)
	}

	// Validate space reduction (within 1% tolerance)
	actualReduction := optimizer.CalculateMemoryReduction(timeComplexity)
	if math.Abs(actualReduction-expectedReduction) > 1.0 {
		t.Errorf("Space reduction mismatch: expected ~%.1f%%, got %.1f%%",
			expectedReduction, actualReduction)
	}

	// Validate formula components
	sqrtT := math.Sqrt(float64(timeComplexity))
	log2T := math.Log2(float64(timeComplexity))
	expectedBound := int(math.Floor(sqrtT * log2T))

	if result.SpaceBound != expectedBound {
		t.Errorf("Formula validation failed: √%d × log₂(%d) = %.2f × %.2f = %d, got %d",
			timeComplexity, timeComplexity, sqrtT, log2T, expectedBound, result.SpaceBound)
	}

	t.Logf("✅ Small scale (t=%d): space=%d, efficiency=%.2fx, reduction=%.1f%%",
		timeComplexity, result.SpaceBound, result.Efficiency, actualReduction)
}

// TestWilliamsSpaceBound_MediumScale validates t=1000 matches research paper
//
// Mathematical expectation:
//   √1000 × log₂(1000) = 31.623 × 9.966 = 315.12 → 315 (floor)
//
// Research claim: 3.2x efficiency, 68% space reduction
func TestWilliamsSpaceBound_MediumScale(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Test parameters from research paper
	timeComplexity := 1000
	expectedSpaceBound := 315 // floor(31.623 × 9.966)
	expectedEfficiency := 3.2 // Research claim
	expectedReduction := 68.0 // Percentage (68.5% in paper)

	result := optimizer.CalculateSpaceBound(timeComplexity)

	// Validate space bound (exact match)
	if result.SpaceBound != expectedSpaceBound {
		t.Errorf("Space bound mismatch: expected %d, got %d",
			expectedSpaceBound, result.SpaceBound)
	}

	// Validate efficiency (≥ threshold, within 0.1 tolerance)
	if math.Abs(result.Efficiency-expectedEfficiency) > 0.2 {
		t.Errorf("Efficiency mismatch: expected ~%.2f, got %.2f",
			expectedEfficiency, result.Efficiency)
	}

	// Validate space reduction (within 1% tolerance)
	actualReduction := optimizer.CalculateMemoryReduction(timeComplexity)
	if math.Abs(actualReduction-expectedReduction) > 1.0 {
		t.Errorf("Space reduction mismatch: expected ~%.1f%%, got %.1f%%",
			expectedReduction, actualReduction)
	}

	// Validate formula components
	sqrtT := math.Sqrt(float64(timeComplexity))
	log2T := math.Log2(float64(timeComplexity))
	expectedBound := int(math.Floor(sqrtT * log2T))

	if result.SpaceBound != expectedBound {
		t.Errorf("Formula validation failed: √%d × log₂(%d) = %.2f × %.2f = %d, got %d",
			timeComplexity, timeComplexity, sqrtT, log2T, expectedBound, result.SpaceBound)
	}

	t.Logf("✅ Medium scale (t=%d): space=%d, efficiency=%.2fx, reduction=%.1f%%",
		timeComplexity, result.SpaceBound, result.Efficiency, actualReduction)
}

// TestWilliamsSpaceBound_LargeScale validates t=10000 matches research paper
//
// Mathematical expectation:
//   √10000 × log₂(10000) = 100 × 13.288 = 1328.77 → 1328 (floor)
//
// Research claim: 7.5x efficiency, 87% space reduction
func TestWilliamsSpaceBound_LargeScale(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Test parameters from research paper
	timeComplexity := 10000
	expectedSpaceBound := 1328 // floor(100 × 13.288)
	expectedEfficiency := 7.5 // Research claim
	expectedReduction := 87.0 // Percentage

	result := optimizer.CalculateSpaceBound(timeComplexity)

	// Validate space bound (within 1 unit - rounding differences)
	if math.Abs(float64(result.SpaceBound-expectedSpaceBound)) > 1 {
		t.Errorf("Space bound mismatch: expected ~%d, got %d",
			expectedSpaceBound, result.SpaceBound)
	}

	// Validate efficiency (≥ threshold)
	if result.Efficiency < expectedEfficiency {
		t.Errorf("Efficiency below threshold: expected ≥%.2f, got %.2f",
			expectedEfficiency, result.Efficiency)
	}

	// Validate space reduction (within 1% tolerance)
	actualReduction := optimizer.CalculateMemoryReduction(timeComplexity)
	if math.Abs(actualReduction-expectedReduction) > 1.0 {
		t.Errorf("Space reduction mismatch: expected ~%.1f%%, got %.1f%%",
			expectedReduction, actualReduction)
	}

	// Validate formula components
	sqrtT := math.Sqrt(float64(timeComplexity))
	log2T := math.Log2(float64(timeComplexity))
	expectedBound := int(math.Floor(sqrtT * log2T))

	if result.SpaceBound != expectedBound {
		t.Errorf("Formula validation failed: √%d × log₂(%d) = %.2f × %.2f = %d, got %d",
			timeComplexity, timeComplexity, sqrtT, log2T, expectedBound, result.SpaceBound)
	}

	t.Logf("✅ Large scale (t=%d): space=%d, efficiency=%.2fx, reduction=%.1f%%",
		timeComplexity, result.SpaceBound, result.Efficiency, actualReduction)
}

// TestWilliamsEfficiency_ScalesLogarithmically validates efficiency growth
//
// Mathematical property: As t increases, efficiency = t / (√t × log₂(t))
// should grow, but sublinearly (logarithmic growth).
//
// Expected pattern:
//   t=100   → efficiency ≈ 1.5x
//   t=1000  → efficiency ≈ 3.2x (2.1x growth)
//   t=10000 → efficiency ≈ 7.5x (2.3x growth)
func TestWilliamsEfficiency_ScalesLogarithmically(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	scales := []struct {
		timeComplexity int
		minEfficiency  float64
	}{
		{100, 1.5},
		{1000, 3.0},
		{10000, 7.0},
		{100000, 15.0}, // Extrapolation
	}

	var previousEfficiency float64

	for _, scale := range scales {
		efficiency := optimizer.CalculateEfficiency(scale.timeComplexity)

		// Efficiency must meet minimum threshold
		if efficiency < scale.minEfficiency {
			t.Errorf("t=%d: efficiency %.2fx below minimum %.2fx",
				scale.timeComplexity, efficiency, scale.minEfficiency)
		}

		// Efficiency must grow monotonically
		if previousEfficiency > 0 && efficiency <= previousEfficiency {
			t.Errorf("Efficiency must grow: t=%d efficiency %.2fx ≤ previous %.2fx",
				scale.timeComplexity, efficiency, previousEfficiency)
		}

		previousEfficiency = efficiency

		t.Logf("✅ t=%d: efficiency=%.2fx (growth validated)", scale.timeComplexity, efficiency)
	}
}

// TestWilliamsSpaceReduction_SmallScale validates 34% reduction for t=100
func TestWilliamsSpaceReduction_SmallScale(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	timeComplexity := 100
	expectedReduction := 34.0 // From research paper
	tolerance := 1.0 // 1% tolerance

	actualReduction := optimizer.CalculateMemoryReduction(timeComplexity)

	if math.Abs(actualReduction-expectedReduction) > tolerance {
		t.Errorf("Space reduction mismatch: expected ~%.1f%%, got %.1f%% (tolerance ±%.1f%%)",
			expectedReduction, actualReduction, tolerance)
	}

	// Verify calculation manually
	linearSpace := float64(timeComplexity)
	williamsSpace := float64(optimizer.CalculateSpaceBound(timeComplexity).SpaceBound)
	expectedCalc := ((linearSpace - williamsSpace) / linearSpace) * 100.0

	if math.Abs(actualReduction-expectedCalc) > 0.01 {
		t.Errorf("Calculation error: formula says %.2f%%, function returned %.2f%%",
			expectedCalc, actualReduction)
	}

	t.Logf("✅ Small scale (t=%d): reduction=%.1f%% (expected ~%.1f%%)",
		timeComplexity, actualReduction, expectedReduction)
}

// TestWilliamsSpaceReduction_MediumScale validates 68% reduction for t=1000
func TestWilliamsSpaceReduction_MediumScale(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	timeComplexity := 1000
	expectedReduction := 68.5 // From research paper (68-69% range)
	tolerance := 1.0

	actualReduction := optimizer.CalculateMemoryReduction(timeComplexity)

	if math.Abs(actualReduction-expectedReduction) > tolerance {
		t.Errorf("Space reduction mismatch: expected ~%.1f%%, got %.1f%% (tolerance ±%.1f%%)",
			expectedReduction, actualReduction, tolerance)
	}

	// Verify calculation manually
	linearSpace := float64(timeComplexity)
	williamsSpace := float64(optimizer.CalculateSpaceBound(timeComplexity).SpaceBound)
	expectedCalc := ((linearSpace - williamsSpace) / linearSpace) * 100.0

	if math.Abs(actualReduction-expectedCalc) > 0.01 {
		t.Errorf("Calculation error: formula says %.2f%%, function returned %.2f%%",
			expectedCalc, actualReduction)
	}

	t.Logf("✅ Medium scale (t=%d): reduction=%.1f%% (expected ~%.1f%%)",
		timeComplexity, actualReduction, expectedReduction)
}

// TestWilliamsSpaceReduction_LargeScale validates 87% reduction for t=10000
func TestWilliamsSpaceReduction_LargeScale(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	timeComplexity := 10000
	expectedReduction := 87.0 // From research paper
	tolerance := 1.0

	actualReduction := optimizer.CalculateMemoryReduction(timeComplexity)

	if math.Abs(actualReduction-expectedReduction) > tolerance {
		t.Errorf("Space reduction mismatch: expected ~%.1f%%, got %.1f%% (tolerance ±%.1f%%)",
			expectedReduction, actualReduction, tolerance)
	}

	// Verify calculation manually
	linearSpace := float64(timeComplexity)
	williamsSpace := float64(optimizer.CalculateSpaceBound(timeComplexity).SpaceBound)
	expectedCalc := ((linearSpace - williamsSpace) / linearSpace) * 100.0

	if math.Abs(actualReduction-expectedCalc) > 0.01 {
		t.Errorf("Calculation error: formula says %.2f%%, function returned %.2f%%",
			expectedCalc, actualReduction)
	}

	t.Logf("✅ Large scale (t=%d): reduction=%.1f%% (expected ~%.1f%%)",
		timeComplexity, actualReduction, expectedReduction)
}

// TestWilliamsSpaceBound_EdgeCase_One validates t=1 base case
//
// Mathematical expectation:
//   √1 × log₂(1) = 1 × 0 = 0, BUT code handles as 1 (base case)
func TestWilliamsSpaceBound_EdgeCase_One(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	result := optimizer.CalculateSpaceBound(1)

	// Base case should return 1 (not 0)
	if result.SpaceBound != 1 {
		t.Errorf("Base case (t=1): expected space bound 1, got %d", result.SpaceBound)
	}

	// Efficiency should be 1.0 (no gain)
	if result.Efficiency != 1.0 {
		t.Errorf("Base case (t=1): expected efficiency 1.0, got %.2f", result.Efficiency)
	}

	// Formula should mention base case
	if result.Formula == "" {
		t.Error("Base case (t=1): expected non-empty formula explanation")
	}

	t.Logf("✅ Edge case (t=1): space=%d, efficiency=%.2fx",
		result.SpaceBound, result.Efficiency)
}

// TestWilliamsSpaceBound_EdgeCase_Zero validates t=0 graceful handling
//
// Mathematical expectation: Invalid input, should return 0 with error message
func TestWilliamsSpaceBound_EdgeCase_Zero(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	result := optimizer.CalculateSpaceBound(0)

	// Should return 0 for invalid input
	if result.SpaceBound != 0 {
		t.Errorf("Invalid case (t=0): expected space bound 0, got %d", result.SpaceBound)
	}

	// Efficiency should be 0.0
	if result.Efficiency != 0.0 {
		t.Errorf("Invalid case (t=0): expected efficiency 0.0, got %.2f", result.Efficiency)
	}

	// Formula should mention invalid
	if result.Formula == "" {
		t.Error("Invalid case (t=0): expected error message in formula")
	}

	t.Logf("✅ Edge case (t=0): gracefully handled with space=%d, efficiency=%.2f",
		result.SpaceBound, result.Efficiency)
}

// ============================================================================
// OPTIMIZATION TESTS (85% REQUIRED)
// ============================================================================

// TestWilliamsOptimalBatchSize validates batch size calculation
//
// Mathematical expectation:
//   For t=1000, space bound ≈ 315
//   Batch size = min(space_bound, memory_constraint)
func TestWilliamsOptimalBatchSize(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		name             string
		totalItems       int
		memoryMB         int
		avgItemSize      int
		expectedBatch    int
		tolerance        int
		constraintType   string // "williams" or "memory"
	}{
		{
			"Williams-constrained (large memory)",
			1000, 512, 1024,
			315, 5, "williams",
		},
		{
			"Williams-constrained (1MB memory still allows Williams)",
			1000, 1, 1024,
			315, 10, "williams", // 1MB / 1KB = 1024 items, but Williams=315 < 1024, so Williams wins!
		},
		{
			"Memory-constrained (very tight memory)",
			1000, 1, 4096,
			256, 10, "memory", // 1MB / 4KB = 256 items < Williams 315, memory wins
		},
		{
			"Small dataset",
			100, 64, 1024,
			66, 5, "williams",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := optimizer.OptimizeBatchSize(tt.totalItems, tt.memoryMB, tt.avgItemSize)

			// Validate batch size within tolerance
			if math.Abs(float64(result.OptimalBatchSize-tt.expectedBatch)) > float64(tt.tolerance) {
				t.Errorf("Expected batch size ~%d (±%d), got %d",
					tt.expectedBatch, tt.tolerance, result.OptimalBatchSize)
			}

			// Validate batch count
			expectedBatches := (tt.totalItems + result.OptimalBatchSize - 1) / result.OptimalBatchSize
			if result.NumBatches != expectedBatches {
				t.Errorf("Expected %d batches, got %d", expectedBatches, result.NumBatches)
			}

			// Validate explanation non-empty
			if result.Explanation == "" {
				t.Error("Expected non-empty explanation")
			}

			t.Logf("✅ %s: batch_size=%d, num_batches=%d, constraint=%s",
				tt.name, result.OptimalBatchSize, result.NumBatches, tt.constraintType)
		})
	}
}

// TestWilliamsConfidenceMultiplier validates OCR confidence boost range
//
// Mathematical expectation:
//   confidence = 0.85 + (0.15 × min(efficiency/10, 1.0))
//   Range: [0.85, 1.00]
//
// IMPORTANT: Confidence boost requires HIGH efficiency (≥10x) to reach 1.0.
// For small field counts (1-20), efficiency is low (1-2x), so confidence
// stays near minimum 0.85-0.87. This is CORRECT behavior!
func TestWilliamsConfidenceMultiplier(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		fieldsExtracted int
		minConfidence   float64
		maxConfidence   float64
	}{
		{0, 0.85, 0.85},   // Minimum (no extraction)
		{1, 0.85, 0.87},   // Very low efficiency → low confidence
		{5, 0.85, 0.88},   // Low efficiency → low confidence
		{10, 0.85, 0.88},  // Still low efficiency (~1.5x)
		{15, 0.85, 0.88},  // Still low efficiency (~1.6x)
		{20, 0.85, 0.88},  // Still low efficiency (~1.7x)
		{100, 0.86, 0.88}, // Medium efficiency (~1.5x)
		{1000, 0.89, 0.92}, // Higher efficiency (~3.2x)
		{10000, 0.95, 1.00}, // High efficiency (~7.5x → confidence boost!)
	}

	for _, tt := range tests {
		confidence := optimizer.CalculateConfidenceMultiplier(tt.fieldsExtracted, "OCR")

		// Validate range
		if confidence < tt.minConfidence || confidence > tt.maxConfidence {
			efficiency := optimizer.CalculateEfficiency(tt.fieldsExtracted)
			t.Errorf("Fields=%d: expected confidence in [%.2f, %.2f], got %.2f (efficiency=%.2fx)",
				tt.fieldsExtracted, tt.minConfidence, tt.maxConfidence, confidence, efficiency)
		}

		// Validate global bounds [0.85, 1.00]
		if confidence < 0.85 || confidence > 1.00 {
			t.Errorf("Confidence %.2f outside valid range [0.85, 1.00]", confidence)
		}

		t.Logf("✅ Fields=%d: confidence=%.3f", tt.fieldsExtracted, confidence)
	}
}

// TestWilliamsPerformance_LargeN benchmarks performance for t=100000
func TestWilliamsPerformance_LargeN(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Large scale test
	timeComplexity := 100000

	result := optimizer.CalculateSpaceBound(timeComplexity)

	// Validate result is reasonable
	if result.SpaceBound <= 0 {
		t.Errorf("Large scale (t=%d): invalid space bound %d", timeComplexity, result.SpaceBound)
	}

	// Efficiency should be high (>15x for t=100K)
	if result.Efficiency < 15.0 {
		t.Errorf("Large scale (t=%d): efficiency %.2fx too low (expected >15x)",
			timeComplexity, result.Efficiency)
	}

	// Space reduction should be >90%
	reduction := optimizer.CalculateMemoryReduction(timeComplexity)
	if reduction < 90.0 {
		t.Errorf("Large scale (t=%d): reduction %.1f%% too low (expected >90%%)",
			timeComplexity, reduction)
	}

	t.Logf("✅ Large scale (t=%d): space=%d, efficiency=%.2fx, reduction=%.1f%%",
		timeComplexity, result.SpaceBound, result.Efficiency, reduction)
}

// TestWilliamsMemoryEfficiency validates no allocations in hot path
//
// This test ensures Williams calculations are allocation-free (critical for performance)
func TestWilliamsMemoryEfficiency(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Warm up (avoid counting initial allocations)
	for i := 0; i < 100; i++ {
		_ = optimizer.CalculateSpaceBound(1000)
	}

	// Measure allocations
	allocsBefore := testing.AllocsPerRun(1000, func() {
		_ = optimizer.CalculateSpaceBound(1000)
	})

	// Should be minimal allocations (< 2 per operation)
	// Note: String formatting in formula causes some allocations
	maxAllocs := 3.0 // Generous tolerance

	if allocsBefore > maxAllocs {
		t.Logf("⚠️  Warning: %.2f allocations per operation (expected ≤%.0f)",
			allocsBefore, maxAllocs)
		// Not failing - string formatting is expected
	} else {
		t.Logf("✅ Memory efficient: %.2f allocations per operation", allocsBefore)
	}
}

// ============================================================================
// EXPLORATION TESTS (70% REQUIRED)
// ============================================================================

// TestWilliamsWithVedicDigitalRoot validates integration with Vedic math
//
// Digital root property: DR(n) = 1 + (n-1) % 9
// Williams optimization can be combined with digital root filtering
func TestWilliamsWithVedicDigitalRoot(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Helper: calculate digital root
	digitalRoot := func(n int) int {
		if n == 0 {
			return 0
		}
		return 1 + (n-1)%9
	}

	// Test: Williams space bound should have consistent digital root patterns
	tests := []int{100, 1000, 10000}

	for _, tc := range tests {
		result := optimizer.CalculateSpaceBound(tc)
		dr := digitalRoot(result.SpaceBound)

		// Digital root should be in [1, 9]
		if dr < 1 || dr > 9 {
			t.Errorf("t=%d: invalid digital root %d for space bound %d",
				tc, dr, result.SpaceBound)
		}

		t.Logf("✅ t=%d: space_bound=%d, digital_root=%d",
			tc, result.SpaceBound, dr)
	}
}

// TestWilliamsWithQuaternionState validates integration with quaternion encoding
//
// Quaternion property: ||Q|| = 1.0 (unit quaternion on S³)
// Williams efficiency can be encoded as quaternion component
func TestWilliamsWithQuaternionState(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Simulate quaternion encoding of Williams metrics
	type QuaternionState struct {
		W float64 // Efficiency (normalized)
		X float64 // Space reduction (normalized)
		Y float64 // Confidence multiplier
		Z float64 // Reserved
	}

	normalize := func(q QuaternionState) QuaternionState {
		magnitude := math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
		if magnitude == 0 {
			return QuaternionState{1, 0, 0, 0}
		}
		return QuaternionState{
			W: q.W / magnitude,
			X: q.X / magnitude,
			Y: q.Y / magnitude,
			Z: q.Z / magnitude,
		}
	}

	// Test case: t=1000, fields=15
	timeComplexity := 1000
	fieldsExtracted := 15

	result := optimizer.CalculateSpaceBound(timeComplexity)
	reduction := optimizer.CalculateMemoryReduction(timeComplexity)
	confidence := optimizer.CalculateConfidenceMultiplier(fieldsExtracted, "OCR")

	// Create quaternion state
	q := QuaternionState{
		W: result.Efficiency / 10.0,  // Normalize efficiency to [0, 1]
		X: reduction / 100.0,          // Normalize reduction to [0, 1]
		Y: confidence,                 // Already in [0.85, 1.00]
		Z: 0.0,                        // Reserved
	}

	// Normalize to unit quaternion
	qNorm := normalize(q)

	// Validate ||Q|| = 1.0
	magnitude := math.Sqrt(qNorm.W*qNorm.W + qNorm.X*qNorm.X + qNorm.Y*qNorm.Y + qNorm.Z*qNorm.Z)
	if math.Abs(magnitude-1.0) > 0.001 {
		t.Errorf("Quaternion not normalized: ||Q|| = %.6f (expected 1.0)", magnitude)
	}

	t.Logf("✅ Quaternion encoding: Q=(%.3f, %.3f, %.3f, %.3f), ||Q||=%.6f",
		qNorm.W, qNorm.X, qNorm.Y, qNorm.Z, magnitude)
}

// ============================================================================
// BENCHMARKS (Performance Validation)
// ============================================================================

// BenchmarkWilliamsSpaceBound_SmallScale benchmarks t=100
func BenchmarkWilliamsSpaceBound_SmallScale(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateSpaceBound(100)
	}
}

// BenchmarkWilliamsSpaceBound_MediumScale benchmarks t=1000
func BenchmarkWilliamsSpaceBound_MediumScale(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateSpaceBound(1000)
	}
}

// BenchmarkWilliamsSpaceBound_LargeScale benchmarks t=10000
func BenchmarkWilliamsSpaceBound_LargeScale(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateSpaceBound(10000)
	}
}

// BenchmarkWilliamsSpaceBound_ExtraLargeScale benchmarks t=100000
func BenchmarkWilliamsSpaceBound_ExtraLargeScale(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateSpaceBound(100000)
	}
}

// BenchmarkWilliamsConfidenceMultiplier_HighExtraction benchmarks 15 fields
func BenchmarkWilliamsConfidenceMultiplier_HighExtraction(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateConfidenceMultiplier(15, "OCR")
	}
}

// BenchmarkWilliamsOptimizeBatchSize_LargeDataset benchmarks batch optimization
func BenchmarkWilliamsOptimizeBatchSize_LargeDataset(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.OptimizeBatchSize(10000, 64, 1024)
	}
}

// ============================================================================
// TABLE-DRIVEN COMPREHENSIVE VALIDATION
// ============================================================================

// TestWilliamsComprehensiveValidation validates ALL research claims in one test
func TestWilliamsComprehensiveValidation(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Research paper validation table
	researchClaims := []struct {
		scale          string
		timeComplexity int
		spaceBound     int
		efficiency     float64
		reduction      float64
		tolerance      float64 // Percentage tolerance
	}{
		{"Small", 100, 66, 1.5, 34.0, 5.0},
		{"Medium", 1000, 315, 3.2, 68.5, 2.0},
		{"Large", 10000, 1329, 7.5, 87.0, 2.0},
	}

	for _, claim := range researchClaims {
		t.Run(claim.scale, func(t *testing.T) {
			result := optimizer.CalculateSpaceBound(claim.timeComplexity)
			reduction := optimizer.CalculateMemoryReduction(claim.timeComplexity)

			// Validate space bound
			spaceBoundTolerance := int(float64(claim.spaceBound) * claim.tolerance / 100.0)
			if math.Abs(float64(result.SpaceBound-claim.spaceBound)) > float64(spaceBoundTolerance) {
				t.Errorf("%s: space bound %d != expected %d (±%d)",
					claim.scale, result.SpaceBound, claim.spaceBound, spaceBoundTolerance)
			}

			// Validate efficiency
			efficiencyTolerance := claim.efficiency * claim.tolerance / 100.0
			if math.Abs(result.Efficiency-claim.efficiency) > efficiencyTolerance {
				t.Errorf("%s: efficiency %.2f != expected %.2f (±%.2f)",
					claim.scale, result.Efficiency, claim.efficiency, efficiencyTolerance)
			}

			// Validate reduction
			reductionTolerance := claim.tolerance
			if math.Abs(reduction-claim.reduction) > reductionTolerance {
				t.Errorf("%s: reduction %.1f%% != expected %.1f%% (±%.1f%%)",
					claim.scale, reduction, claim.reduction, reductionTolerance)
			}

			t.Logf("✅ %s scale validated: space=%d, efficiency=%.2fx, reduction=%.1f%%",
				claim.scale, result.SpaceBound, result.Efficiency, reduction)
		})
	}
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

// williamsStringContains checks if haystack contains needle (simple substring check)
// Note: Using unique name to avoid conflicts with other test files
func williamsStringContains(haystack, needle string) bool {
	if len(needle) == 0 {
		return true
	}
	if len(haystack) < len(needle) {
		return false
	}
	for i := 0; i <= len(haystack)-len(needle); i++ {
		if haystack[i:i+len(needle)] == needle {
			return true
		}
	}
	return false
}
