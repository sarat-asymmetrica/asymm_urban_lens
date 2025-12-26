// Package intelligence - Williams Drift Detector Tests
package intelligence

import (
	"fmt"
	"math"
	"testing"
)

// TestDriftCalculateSpaceBound verifies Williams space optimization formula for drift
func TestDriftCalculateSpaceBound(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	tests := []struct {
		name              string
		t                 int
		expectedThreshold float64 // Approximate
		minEfficiency     float64
		minReduction      float64
	}{
		{
			name:              "Small scale (100 ops)",
			t:                 100,
			expectedThreshold: 66.0,  // √100 × log₂(100) ≈ 10 × 6.64
			minEfficiency:     1.5,   // Should be ~1.5x
			minReduction:      30.0,  // Should save ~34%
		},
		{
			name:              "Medium scale (1,000 ops)",
			t:                 1000,
			expectedThreshold: 316.0, // √1000 × log₂(1000) ≈ 31.6 × 9.97
			minEfficiency:     3.0,   // Should be ~3.2x
			minReduction:      65.0,  // Should save ~68%
		},
		{
			name:              "Large scale (10,000 ops)",
			t:                 10000,
			expectedThreshold: 1330.0, // √10000 × log₂(10000) ≈ 100 × 13.3
			minEfficiency:     7.0,    // Should be ~7.5x
			minReduction:      85.0,   // Should save ~87%
		},
		{
			name:              "Edge case (t=1)",
			t:                 1,
			expectedThreshold: 0.0,
			minEfficiency:     0.0,
			minReduction:      0.0,
		},
		{
			name:              "Edge case (t=0)",
			t:                 0,
			expectedThreshold: 0.0,
			minEfficiency:     0.0,
			minReduction:      0.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := detector.CalculateSpaceBound(tt.t)

			// Verify Williams threshold is in expected range
			if tt.t > 1 {
				if result.WilliamsThreshold < tt.expectedThreshold*0.9 ||
					result.WilliamsThreshold > tt.expectedThreshold*1.1 {
					t.Errorf("WilliamsThreshold = %.2f, want ~%.2f",
						result.WilliamsThreshold, tt.expectedThreshold)
				}
			}

			// Verify efficiency meets minimum
			if result.Efficiency < tt.minEfficiency {
				t.Errorf("Efficiency = %.2f, want >= %.2f",
					result.Efficiency, tt.minEfficiency)
			}

			// Verify space reduction meets minimum
			if result.SpaceReduction < tt.minReduction {
				t.Errorf("SpaceReduction = %.2f%%, want >= %.2f%%",
					result.SpaceReduction, tt.minReduction)
			}

			// Verify optimal batch size is reasonable
			if tt.t > 0 {
				expected := int(math.Ceil(result.WilliamsThreshold))
				if result.OptimalBatchSize != expected {
					t.Errorf("OptimalBatchSize = %d, want %d",
						result.OptimalBatchSize, expected)
				}
			}
		})
	}
}

// TestDriftCalculateConfidenceMultiplier verifies OCR-style confidence boost for drift
func TestDriftCalculateConfidenceMultiplier(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	tests := []struct {
		name           string
		numFields      int
		regime         string
		minMultiplier  float64
		maxMultiplier  float64
	}{
		{
			name:          "Few fields, exploration",
			numFields:     5,
			regime:        "exploration",
			minMultiplier: 0.85,
			maxMultiplier: 0.88,
		},
		{
			name:          "Moderate fields, optimization",
			numFields:     10,
			regime:        "optimization",
			minMultiplier: 0.86,
			maxMultiplier: 0.90,
		},
		{
			name:          "Many fields, stabilization",
			numFields:     20,
			regime:        "stabilization",
			minMultiplier: 0.88,
			maxMultiplier: 0.95,
		},
		{
			name:          "Very many fields, stabilization",
			numFields:     50,
			regime:        "stabilization",
			minMultiplier: 0.90,
			maxMultiplier: 1.00,
		},
		{
			name:          "Edge case (0 fields)",
			numFields:     0,
			regime:        "stabilization",
			minMultiplier: 0.85,
			maxMultiplier: 0.87,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			multiplier := detector.CalculateConfidenceMultiplier(tt.numFields, tt.regime)

			// Verify multiplier is in expected range
			if multiplier < tt.minMultiplier || multiplier > tt.maxMultiplier {
				t.Errorf("CalculateConfidenceMultiplier(%d, %s) = %.4f, want [%.4f, %.4f]",
					tt.numFields, tt.regime, multiplier, tt.minMultiplier, tt.maxMultiplier)
			}

			// Verify multiplier is always in valid range [0.85, 1.0]
			if multiplier < 0.85 || multiplier > 1.0 {
				t.Errorf("CalculateConfidenceMultiplier(%d, %s) = %.4f, outside valid range [0.85, 1.0]",
					tt.numFields, tt.regime, multiplier)
			}
		})
	}
}

// TestShouldRelaxConfidence verifies drift-based confidence relaxation
func TestShouldRelaxConfidence(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	tests := []struct {
		name            string
		baselineMatches int
		currentMatches  int
		queriesRun      int
		shouldRelax     bool
		minThreshold    float64
		maxThreshold    float64
	}{
		{
			name:            "Zero matches, high drift (RELAX)",
			baselineMatches: 10,
			currentMatches:  0,
			queriesRun:      50,
			shouldRelax:     true,
			minThreshold:    0.60,
			maxThreshold:    0.75,
		},
		{
			name:            "Low matches, moderate drift (RELAX)",
			baselineMatches: 10,
			currentMatches:  3,
			queriesRun:      50,
			shouldRelax:     true,
			minThreshold:    0.65,
			maxThreshold:    0.78,
		},
		{
			name:            "Close to baseline, low drift (NO RELAX)",
			baselineMatches: 10,
			currentMatches:  9,
			queriesRun:      50,
			shouldRelax:     false,
			minThreshold:    0.80,
			maxThreshold:    0.80,
		},
		{
			name:            "Exact baseline, zero drift (NO RELAX)",
			baselineMatches: 10,
			currentMatches:  10,
			queriesRun:      50,
			shouldRelax:     false,
			minThreshold:    0.80,
			maxThreshold:    0.80,
		},
		{
			name:            "Higher than baseline (NO RELAX)",
			baselineMatches: 10,
			currentMatches:  15,
			queriesRun:      50,
			shouldRelax:     false,
			minThreshold:    0.80,
			maxThreshold:    0.80,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			relaxation := detector.ShouldRelaxConfidence(
				tt.baselineMatches,
				tt.currentMatches,
				tt.queriesRun,
			)

			// Verify relax decision
			if relaxation.ShouldRelax != tt.shouldRelax {
				t.Errorf("ShouldRelax = %v, want %v (drift: %.2f%%)",
					relaxation.ShouldRelax, tt.shouldRelax, relaxation.DriftPercent)
			}

			// Verify threshold is in expected range
			if relaxation.RelaxedThreshold < tt.minThreshold ||
				relaxation.RelaxedThreshold > tt.maxThreshold {
				t.Errorf("RelaxedThreshold = %.2f, want [%.2f, %.2f]",
					relaxation.RelaxedThreshold, tt.minThreshold, tt.maxThreshold)
			}

			// Verify original threshold is always 0.80
			if relaxation.OriginalThreshold != 0.80 {
				t.Errorf("OriginalThreshold = %.2f, want 0.80",
					relaxation.OriginalThreshold)
			}

			// Verify rationale is present
			if len(relaxation.Rationale) == 0 {
				t.Error("Rationale is empty, want descriptive explanation")
			}

			// Verify relaxed threshold never goes below 0.50
			if relaxation.RelaxedThreshold < 0.50 {
				t.Errorf("RelaxedThreshold = %.2f, below minimum 0.50",
					relaxation.RelaxedThreshold)
			}
		})
	}
}

// TestCheckMergeDrift verifies drift detection for merge approval
func TestCheckMergeDrift(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	tests := []struct {
		name       string
		newMatches int
		approved   bool
	}{
		{
			name:       "Very close to baseline (APPROVE)",
			newMatches: 10,
			approved:   true,
		},
		{
			name:       "Slightly below baseline (APPROVE)",
			newMatches: 9,
			approved:   true,
		},
		{
			name:       "Slightly above baseline (APPROVE)",
			newMatches: 11,
			approved:   true,
		},
		{
			name:       "Moderately below baseline (depends on Williams threshold)",
			newMatches: 7,
			approved:   true, // Should be within 5% threshold initially
		},
		{
			name:       "Far from baseline (REJECT)",
			newMatches: 0,
			approved:   false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := detector.CheckMergeDrift("team_test", tt.newMatches)

			// Verify approval decision
			if result.Approved != tt.approved {
				t.Errorf("Approved = %v, want %v (drift: %.2f%%, threshold: %.2f%%)",
					result.Approved, tt.approved, result.Drift, result.Threshold)
			}

			// Verify Williams value is calculated
			if result.WilliamsValue < 0 {
				t.Errorf("WilliamsValue = %.2f, want >= 0", result.WilliamsValue)
			}

			// Verify recommendation matches approval
			if result.Approved && result.Recommended != "APPROVE" {
				t.Errorf("Approved=true but Recommended=%s, want APPROVE",
					result.Recommended)
			}
			if !result.Approved && result.Recommended != "REVIEW_REQUIRED" {
				t.Errorf("Approved=false but Recommended=%s, want REVIEW_REQUIRED",
					result.Recommended)
			}
		})
	}
}

// TestUpdateBaseline verifies baseline tracking
func TestUpdateBaseline(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	// Verify initial baseline
	baseline := detector.GetBaseline()
	if baseline.GlobalMatches != 10 {
		t.Errorf("Initial GlobalMatches = %d, want 10", baseline.GlobalMatches)
	}
	if baseline.CommitsSinceUpdate != 0 {
		t.Errorf("Initial CommitsSinceUpdate = %d, want 0", baseline.CommitsSinceUpdate)
	}

	// Update baseline
	detector.UpdateBaseline(15)

	// Verify update
	baseline = detector.GetBaseline()
	if baseline.GlobalMatches != 15 {
		t.Errorf("After update GlobalMatches = %d, want 15", baseline.GlobalMatches)
	}
	if baseline.CommitsSinceUpdate != 1 {
		t.Errorf("After update CommitsSinceUpdate = %d, want 1", baseline.CommitsSinceUpdate)
	}

	// Update again
	detector.UpdateBaseline(12)

	// Verify second update
	baseline = detector.GetBaseline()
	if baseline.GlobalMatches != 12 {
		t.Errorf("After 2nd update GlobalMatches = %d, want 12", baseline.GlobalMatches)
	}
	if baseline.CommitsSinceUpdate != 2 {
		t.Errorf("After 2nd update CommitsSinceUpdate = %d, want 2", baseline.CommitsSinceUpdate)
	}
}

// TestTokenEconomics verifies the 10% upfront / 90% savings principle
func TestTokenEconomics(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	// Scenario: Zero matches found (stub generation path)
	relaxation := detector.ShouldRelaxConfidence(10, 0, 50)

	if !relaxation.ShouldRelax {
		t.Error("Token Economics: Should relax confidence to avoid stub generation")
	}

	// Verify relaxation amount represents ~10% increase in search space
	originalSpace := 1.0 - 0.80 // 20% of patterns excluded
	relaxedSpace := 1.0 - relaxation.RelaxedThreshold
	increase := (relaxedSpace - originalSpace) / originalSpace * 100.0

	if increase < 25.0 { // Should expand search space by at least 25%
		t.Errorf("Token Economics: Search space increase = %.1f%%, want >= 25%%", increase)
	}

	t.Logf("Token Economics Validation:")
	t.Logf("  Original threshold: %.2f (excludes %.0f%% of patterns)",
		0.80, (1.0-0.80)*100.0)
	t.Logf("  Relaxed threshold: %.2f (excludes %.0f%% of patterns)",
		relaxation.RelaxedThreshold, (1.0-relaxation.RelaxedThreshold)*100.0)
	t.Logf("  Search space increase: %.1f%%", increase)
	t.Logf("  Rationale: %s", relaxation.Rationale)
}

// TestFibonacciCascade verifies relaxation follows Fibonacci-like progression
func TestFibonacciCascade(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	// Test progressive relaxation at different drift levels
	tests := []struct {
		drift          int
		expectedRange  [2]float64 // [min, max]
	}{
		{drift: 0, expectedRange: [2]float64{0.80, 0.80}},   // No drift
		{drift: 3, expectedRange: [2]float64{0.70, 0.78}},   // Small drift
		{drift: 7, expectedRange: [2]float64{0.60, 0.75}},   // Moderate drift
		{drift: 10, expectedRange: [2]float64{0.50, 0.70}},  // Large drift
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("Drift=%d", tt.drift), func(t *testing.T) {
			relaxation := detector.ShouldRelaxConfidence(10, 10-tt.drift, 50)

			if relaxation.RelaxedThreshold < tt.expectedRange[0] ||
				relaxation.RelaxedThreshold > tt.expectedRange[1] {
				t.Errorf("Fibonacci Cascade: drift=%d, threshold=%.2f, want [%.2f, %.2f]",
					tt.drift, relaxation.RelaxedThreshold, tt.expectedRange[0], tt.expectedRange[1])
			}

			t.Logf("Drift=%d: Relaxed %.2f → %.2f (%.1f%% drift)",
				tt.drift, relaxation.OriginalThreshold, relaxation.RelaxedThreshold, relaxation.DriftPercent)
		})
	}
}

// TestRegimeSpecificBehavior verifies regime-specific confidence adjustments
func TestRegimeSpecificBehavior(t *testing.T) {
	detector := NewWilliamsDriftDetector(10)

	regimes := []string{"exploration", "optimization", "stabilization"}
	numFields := 20

	var previousMultiplier float64
	for i, regime := range regimes {
		multiplier := detector.CalculateConfidenceMultiplier(numFields, regime)

		t.Logf("%s regime: multiplier = %.4f", regime, multiplier)

		// Verify increasing strictness: exploration < optimization < stabilization
		if i > 0 && multiplier <= previousMultiplier {
			t.Errorf("Regime %s multiplier (%.4f) should be > previous regime (%.4f)",
				regime, multiplier, previousMultiplier)
		}

		previousMultiplier = multiplier
	}
}
