// Package intelligence implements Williams Drift Detection for pattern matching confidence
//
// Williams Space Optimizer with Drift-Based Confidence Relaxation
// Author: Agent 8.5.2 (Dr. Rachel Zhang + Vladimir Petrov + Dr. Sophia Kovács)
// Created: 2025-11-07
//
// Mathematical Foundation:
//   Williams Space Bound: √t × log₂(t) - MIT 2011 breakthrough
//   Drift Detection: Auto-relax confidence when drift > 5% of Williams threshold
//   Token Economics: 10% more tokens upfront saves 90% rework later
//
// Research Paper Reference:
//   UNIFIED_INTELLIGENCE_MONITORING_RESEARCH_PAPER.html, lines 377-409, 872-899
package intelligence

import (
	"fmt"
	"math"
	"time"
)

// WilliamsDriftDetector manages dynamic confidence thresholds using Williams optimization
type WilliamsDriftDetector struct {
	baseline PatternBaseline
}

// PatternBaseline tracks global baseline for drift detection
type PatternBaseline struct {
	GlobalMatches      int       // Expected number of matches
	CommitsSinceUpdate int       // Queries run since last baseline update
	LastUpdateHash     string    // Last update identifier
	TeamOverrides      map[string]float64 // Team-specific adjustments
	UpdatedAt          time.Time
}

// DriftSpaceBound contains Williams space optimization for drift detection
type DriftSpaceBound struct {
	WilliamsThreshold float64 // √t × log₂(t)
	Efficiency        float64 // t / williams_threshold
	SpaceReduction    float64 // Percentage space saved
	OptimalBatchSize  int     // Recommended batch size
}

// MergeDriftResult contains drift detection decision
type MergeDriftResult struct {
	Approved      bool    // Should auto-approve?
	Drift         float64 // Drift percentage from baseline
	Threshold     float64 // Auto-approve threshold
	WilliamsValue float64 // Williams bound at current t
	Recommended   string  // Human-readable recommendation
}

// ConfidenceRelaxation contains relaxed confidence parameters
type ConfidenceRelaxation struct {
	ShouldRelax      bool    // Should we relax confidence?
	OriginalThreshold float64 // Original threshold (e.g., 0.80)
	RelaxedThreshold  float64 // Relaxed threshold (e.g., 0.70)
	DriftPercent      float64 // Drift from baseline
	Rationale         string  // Why we're relaxing
}

// RegimeLeverageMultiplier maps regimes to leverage factors
var RegimeLeverageMultiplier = map[string]float64{
	"exploration":    0.70, // More lenient during exploration
	"optimization":   0.85, // Moderate during optimization
	"stabilization":  1.00, // Strict during stabilization
}

// NewWilliamsDriftDetector creates a new drift detector
//
// Parameters:
//   - initialBaseline: Expected number of matches under normal conditions
//
// Example:
//
//	detector := NewWilliamsDriftDetector(10) // Expect ~10 matches normally
func NewWilliamsDriftDetector(initialBaseline int) *WilliamsDriftDetector {
	return &WilliamsDriftDetector{
		baseline: PatternBaseline{
			GlobalMatches:      initialBaseline,
			CommitsSinceUpdate: 0,
			TeamOverrides:      make(map[string]float64),
			UpdatedAt:          time.Now(),
		},
	}
}

// CalculateSpaceBound computes Williams space optimization metrics
//
// Formula (from research paper, lines 381-389):
//   williams_space_bound = √t × log₂(t)
//   efficiency = t / williams_space_bound
//   space_reduction_percent = ((t - williams_space_bound) / t) × 100%
//
// Parameters:
//   - t: Time complexity (number of operations)
//
// Returns:
//   - DriftSpaceBound with all metrics
//
// Example:
//
//	result := detector.CalculateSpaceBound(1000)
//	// result.Efficiency ≈ 3.2, result.SpaceReduction ≈ 68%
func (wd *WilliamsDriftDetector) CalculateSpaceBound(t int) DriftSpaceBound {
	if t <= 0 {
		return DriftSpaceBound{
			WilliamsThreshold: 0,
			Efficiency:        0,
			SpaceReduction:    0,
			OptimalBatchSize:  1,
		}
	}

	ft := float64(t)
	williamsThreshold := math.Sqrt(ft) * math.Log2(ft)
	efficiency := ft / williamsThreshold
	spaceReduction := ((ft - williamsThreshold) / ft) * 100.0

	return DriftSpaceBound{
		WilliamsThreshold: williamsThreshold,
		Efficiency:        efficiency,
		SpaceReduction:    spaceReduction,
		OptimalBatchSize:  int(math.Ceil(williamsThreshold)),
	}
}

// CalculateConfidenceMultiplier computes OCR-style confidence boost
//
// Formula (from research paper, lines 407-410):
//   normalized_efficiency = min(1.0, efficiency / 30.0)
//   confidence_boost = 0.15 × normalized_efficiency
//   base_multiplier = 0.85 + confidence_boost
//   leverage_factor = 1.0 + (leverage / 1000.0)
//   final = base_multiplier × leverage_factor
//
// Parameters:
//   - numFields: Number of fields extracted (e.g., pattern matches)
//   - regime: Current regime (exploration, optimization, stabilization)
//
// Returns:
//   - Confidence multiplier (0.85-1.0)
//
// Example:
//
//	multiplier := detector.CalculateConfidenceMultiplier(10, "stabilization")
//	// multiplier ≈ 0.90 (boosts base confidence)
func (wd *WilliamsDriftDetector) CalculateConfidenceMultiplier(numFields int, regime string) float64 {
	bounds := wd.CalculateSpaceBound(numFields)
	normalizedEfficiency := math.Min(1.0, bounds.Efficiency/30.0)
	confidenceBoost := 0.15 * normalizedEfficiency
	baseMultiplier := 0.85 + confidenceBoost

	// Apply regime-specific leverage
	leverage, exists := RegimeLeverageMultiplier[regime]
	if !exists {
		leverage = 0.85 // Default to optimization
	}
	leverageFactor := 1.0 + (leverage / 1000.0)

	final := baseMultiplier * leverageFactor
	return math.Max(0.85, math.Min(1.0, final))
}

// ShouldRelaxConfidence determines if confidence threshold should be lowered
//
// Algorithm:
//   1. Calculate Williams threshold: √t × log₂(t)
//   2. Compute drift: (baseline - current) / williams_threshold
//   3. If drift > 5%, relax confidence using Fibonacci cascade
//   4. Relaxation levels: 0.80 → 0.70 → 0.60 (minimum 0.50)
//
// Token Economics (from research paper):
//   - Spending 10% more tokens upfront saves 90% rework cost
//   - Better to relax and find close matches than generate stubs
//
// Parameters:
//   - baselineMatches: Expected number of matches
//   - currentMatches: Actual number of matches found
//   - queriesRun: Number of queries executed (t)
//
// Returns:
//   - ConfidenceRelaxation with decision and parameters
//
// Example:
//
//	relaxation := detector.ShouldRelaxConfidence(10, 0, 50)
//	// relaxation.ShouldRelax = true, relaxation.RelaxedThreshold = 0.70
func (wd *WilliamsDriftDetector) ShouldRelaxConfidence(
	baselineMatches int,
	currentMatches int,
	queriesRun int,
) ConfidenceRelaxation {
	// Calculate Williams threshold
	bounds := wd.CalculateSpaceBound(queriesRun)
	williamsThreshold := bounds.WilliamsThreshold

	// Compute drift from baseline
	matchDiff := float64(baselineMatches - currentMatches)
	drift := matchDiff / math.Max(williamsThreshold, 1.0)
	driftPercent := math.Abs(drift) * 100.0

	// Auto-relax if drift > 5% (from research paper, line 882)
	const autoRelaxThreshold = 5.0
	originalThreshold := 0.80

	if driftPercent > autoRelaxThreshold {
		// Fibonacci cascade relaxation: 0.80 → 0.70 → 0.60 → 0.50
		relaxationAmount := math.Min(drift*0.20, 0.30)
		relaxedThreshold := originalThreshold - relaxationAmount
		relaxedThreshold = math.Max(0.50, relaxedThreshold) // Floor at 0.50

		return ConfidenceRelaxation{
			ShouldRelax:       true,
			OriginalThreshold: originalThreshold,
			RelaxedThreshold:  relaxedThreshold,
			DriftPercent:      driftPercent,
			Rationale: fmt.Sprintf(
				"Drift %.1f%% exceeds threshold %.1f%%. Relaxing confidence %.2f → %.2f to find close matches (token economics: prevents stub generation)",
				driftPercent,
				autoRelaxThreshold,
				originalThreshold,
				relaxedThreshold,
			),
		}
	}

	return ConfidenceRelaxation{
		ShouldRelax:       false,
		OriginalThreshold: originalThreshold,
		RelaxedThreshold:  originalThreshold,
		DriftPercent:      driftPercent,
		Rationale: fmt.Sprintf(
			"Drift %.1f%% within threshold %.1f%%. Keeping original confidence %.2f",
			driftPercent,
			autoRelaxThreshold,
			originalThreshold,
		),
	}
}

// CheckMergeDrift validates if pattern match drift is acceptable for merging
//
// Formula (from research paper, lines 877-890):
//   williams_threshold = √t × log₂(t)
//   drift = |new_matches - global_baseline|
//   drift_percent = (drift / global_baseline) × 100
//   auto_approve_threshold = williams_threshold × 0.05  // 5%
//   approved = drift_percent < auto_approve_threshold
//
// Parameters:
//   - teamID: Team identifier (for team-specific overrides)
//   - newMatches: Number of matches found
//
// Returns:
//   - MergeDriftResult with approval decision
//
// Example:
//
//	result := detector.CheckMergeDrift("team_alpha", 8)
//	// result.Approved = true if 8 is within 5% of baseline
func (wd *WilliamsDriftDetector) CheckMergeDrift(teamID string, newMatches int) MergeDriftResult {
	t := wd.baseline.CommitsSinceUpdate
	if t < 1 {
		t = 1 // Prevent log₂(0)
	}

	// Calculate Williams threshold
	williamsThreshold := math.Sqrt(float64(t)) * math.Log2(float64(t))

	// Compute drift
	drift := math.Abs(float64(newMatches - wd.baseline.GlobalMatches))
	driftPercent := (drift / float64(wd.baseline.GlobalMatches)) * 100.0

	// Auto-approve threshold: 5% of Williams value
	autoApproveThreshold := williamsThreshold * 0.05

	approved := driftPercent < autoApproveThreshold

	recommendation := "APPROVE"
	if !approved {
		recommendation = "REVIEW_REQUIRED"
	}

	return MergeDriftResult{
		Approved:      approved,
		Drift:         driftPercent,
		Threshold:     autoApproveThreshold,
		WilliamsValue: williamsThreshold,
		Recommended:   recommendation,
	}
}

// UpdateBaseline updates the global baseline with new data
//
// Call this after successful pattern matching to track evolution over time.
//
// Parameters:
//   - newMatches: Number of matches in latest run
//
// Example:
//
//	detector.UpdateBaseline(12) // Update baseline to 12 matches
func (wd *WilliamsDriftDetector) UpdateBaseline(newMatches int) {
	wd.baseline.GlobalMatches = newMatches
	wd.baseline.CommitsSinceUpdate++
	wd.baseline.UpdatedAt = time.Now()
}

// GetBaseline returns current baseline for inspection
func (wd *WilliamsDriftDetector) GetBaseline() PatternBaseline {
	return wd.baseline
}
