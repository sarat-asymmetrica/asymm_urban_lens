// Package intelligence implements the Unified Intelligence Monitoring System
//
// System Health Metric (SHM) Calculator:
// Aggregates 6 sonar scores into unified quality metric using weighted average.
//
// Weights (from research paper):
//   UX: 0.25, Design: 0.25, Code: 0.125, Semantic: 0.125, Journey: 0.125, State: 0.125
//
// Regime Determination:
//   SHM < 0.70 → EXPLORATION (experimenting, high churn)
//   0.70 ≤ SHM < 0.85 → OPTIMIZATION (improving, moderate stability)
//   SHM ≥ 0.85 → STABILIZATION (production-ready, high reliability)
//
// Research: UNIFIED_INTELLIGENCE_MONITORING_RESEARCH_PAPER.html (Section 2.5)
// Author: Multi-Team Dashboard Generator (AsymmBill)
// Date: 2025-11-07
package intelligence

import (
	"context"
	"fmt"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/intelligence/sonars"
)

// SHMCalculator computes System Health Metric from 6 sonar scores
type SHMCalculator struct {
	uxSonar       *sonars.UXSonar
	designSonar   *sonars.DesignSonar
	codeSonar     *sonars.CodeSonar
	semanticSonar *sonars.SemanticSonar
	journeySonar  *sonars.JourneySonar
	stateSonar    *sonars.StateSonar

	// Weights from research (UX + Design = 50%, internal quality = 50%)
	weights map[string]float64
}

// NewSHMCalculator creates SHM calculator with all 6 sonars
func NewSHMCalculator() *SHMCalculator {
	return &SHMCalculator{
		uxSonar:       sonars.NewUXSonar(),
		designSonar:   sonars.NewDesignSonar(),
		codeSonar:     sonars.NewCodeSonar(),
		semanticSonar: sonars.NewSemanticSonar(),
		journeySonar:  sonars.NewJourneySonar(),
		stateSonar:    sonars.NewStateSonar(),

		weights: map[string]float64{
			"ux":       0.25,  // User-facing (25%)
			"design":   0.25,  // User-facing (25%)
			"code":     0.125, // Internal quality (12.5%)
			"semantic": 0.125, // Internal quality (12.5%)
			"journey":  0.125, // Internal quality (12.5%)
			"state":    0.125, // Internal quality (12.5%)
		},
	}
}

// SHMResult contains comprehensive system health analysis
type SHMResult struct {
	SHM              float64                         // Overall system health metric (0.0-1.0)
	Regime           Regime                          // Exploration, Optimization, or Stabilization
	SonarScores      map[string]float64              // Individual sonar scores
	SonarReports     map[string]*sonars.Report       // Detailed reports from each sonar
	WeakestDimension string                          // Which sonar scored lowest
	StrongestDimension string                        // Which sonar scored highest
	Timestamp        time.Time                       // When analysis was performed
	Duration         time.Duration                   // Total analysis duration
}

// Regime represents development phase based on SHM
type Regime string

const (
	RegimeExploration   Regime = "EXPLORATION"   // SHM < 0.70 (experimenting)
	RegimeOptimization  Regime = "OPTIMIZATION"  // 0.70 ≤ SHM < 0.85 (improving)
	RegimeStabilization Regime = "STABILIZATION" // SHM ≥ 0.85 (production-ready)
)

// CalculateSHM runs all 6 sonars and computes system health metric
func (shm *SHMCalculator) CalculateSHM(ctx context.Context, app *sonars.AppState) (*SHMResult, error) {
	startTime := time.Now()

	// Run all 6 sonars in parallel (conceptually - could use goroutines)
	uxResult, err := sonars.ExecuteFullSonar(ctx, shm.uxSonar, app)
	if err != nil {
		return nil, fmt.Errorf("UX sonar failed: %w", err)
	}

	designResult, err := sonars.ExecuteFullSonar(ctx, shm.designSonar, app)
	if err != nil {
		return nil, fmt.Errorf("design sonar failed: %w", err)
	}

	codeResult, err := sonars.ExecuteFullSonar(ctx, shm.codeSonar, app)
	if err != nil {
		return nil, fmt.Errorf("code sonar failed: %w", err)
	}

	semanticResult, err := sonars.ExecuteFullSonar(ctx, shm.semanticSonar, app)
	if err != nil {
		return nil, fmt.Errorf("semantic sonar failed: %w", err)
	}

	journeyResult, err := sonars.ExecuteFullSonar(ctx, shm.journeySonar, app)
	if err != nil {
		return nil, fmt.Errorf("journey sonar failed: %w", err)
	}

	stateResult, err := sonars.ExecuteFullSonar(ctx, shm.stateSonar, app)
	if err != nil {
		return nil, fmt.Errorf("state sonar failed: %w", err)
	}

	// Collect scores
	scores := map[string]float64{
		"ux":       uxResult.Score,
		"design":   designResult.Score,
		"code":     codeResult.Score,
		"semantic": semanticResult.Score,
		"journey":  journeyResult.Score,
		"state":    stateResult.Score,
	}

	// Collect reports
	reports := map[string]*sonars.Report{
		"ux":       uxResult.Report,
		"design":   designResult.Report,
		"code":     codeResult.Report,
		"semantic": semanticResult.Report,
		"journey":  journeyResult.Report,
		"state":    stateResult.Report,
	}

	// Calculate weighted SHM
	shmValue := shm.computeWeightedSHM(scores)

	// Determine regime
	regime := shm.determineRegime(shmValue)

	// Find weakest and strongest dimensions
	weakest, strongest := shm.findExtremes(scores)

	return &SHMResult{
		SHM:                shmValue,
		Regime:             regime,
		SonarScores:        scores,
		SonarReports:       reports,
		WeakestDimension:   weakest,
		StrongestDimension: strongest,
		Timestamp:          time.Now(),
		Duration:           time.Since(startTime),
	}, nil
}

// computeWeightedSHM calculates weighted average of sonar scores
//
// Formula: SHM = Σ(score × weight) / Σ(weights)
//
// This gives UX and Design more weight (50% combined) than internal quality (50% combined)
func (shm *SHMCalculator) computeWeightedSHM(scores map[string]float64) float64 {
	weightedSum := 0.0
	totalWeight := 0.0

	for sonar, score := range scores {
		weight := shm.weights[sonar]
		weightedSum += score * weight
		totalWeight += weight
	}

	if totalWeight == 0.0 {
		return 0.0
	}

	return weightedSum / totalWeight
}

// determineRegime classifies development phase based on SHM
func (shm *SHMCalculator) determineRegime(shmValue float64) Regime {
	if shmValue < 0.70 {
		return RegimeExploration
	} else if shmValue < 0.85 {
		return RegimeOptimization
	} else {
		return RegimeStabilization
	}
}

// findExtremes identifies weakest and strongest sonar dimensions
func (shm *SHMCalculator) findExtremes(scores map[string]float64) (weakest, strongest string) {
	minScore := 1.0
	maxScore := 0.0

	for sonar, score := range scores {
		if score < minScore {
			minScore = score
			weakest = sonar
		}
		if score > maxScore {
			maxScore = score
			strongest = sonar
		}
	}

	return weakest, strongest
}

// GenerateDashboard creates unified dashboard visualization
func (shm *SHMCalculator) GenerateDashboard(result *SHMResult) string {
	dashboard := "\n"
	dashboard += "┌─────────────────────────────────────────────────────────────┐\n"
	dashboard += "│           UNIFIED INTELLIGENCE MONITORING SYSTEM             │\n"
	dashboard += "│                  (Ananta Sonar Suite)                        │\n"
	dashboard += "└─────────────────────────────────────────────────────────────┘\n"
	dashboard += "\n"

	// System Health Metric
	dashboard += fmt.Sprintf("🎯 System Health Metric (SHM): %.3f\n", result.SHM)
	dashboard += fmt.Sprintf("📊 Regime: %s\n", result.Regime)
	dashboard += fmt.Sprintf("⏱️  Analysis Duration: %v\n", result.Duration)
	dashboard += "\n"

	// Regime explanation
	dashboard += "Regime Guide:\n"
	dashboard += "  • EXPLORATION   (< 0.70): Experimenting with features, high churn expected\n"
	dashboard += "  • OPTIMIZATION  (0.70-0.85): Improving quality, moderate stability\n"
	dashboard += "  • STABILIZATION (≥ 0.85): Production-ready, high reliability\n"
	dashboard += "\n"

	// Sonar scores breakdown
	dashboard += "┌─────────────────────────────────────────────────────────────┐\n"
	dashboard += "│                      SIX SONAR ENGINES                       │\n"
	dashboard += "├────────────────────┬────────┬────────┬─────────────────────┤\n"
	dashboard += "│ Sonar              │ Score  │ Weight │ Status              │\n"
	dashboard += "├────────────────────┼────────┼────────┼─────────────────────┤\n"

	sonars := []string{"ux", "design", "code", "semantic", "journey", "state"}
	sonarNames := map[string]string{
		"ux":       "UX Sonar",
		"design":   "Design Sonar",
		"code":     "Code Sonar",
		"semantic": "Semantic Sonar",
		"journey":  "Journey Sonar",
		"state":    "State Sonar",
	}

	for _, sonar := range sonars {
		score := result.SonarScores[sonar]
		weight := shm.weights[sonar]
		report := result.SonarReports[sonar]

		name := sonarNames[sonar]
		status := string(report.Status)

		// Add sparkline indicator
		indicator := shm.scoreIndicator(score)

		dashboard += fmt.Sprintf("│ %-18s │ %.3f  │ %.3f  │ %-11s %s │\n",
			name, score, weight, status, indicator)
	}

	dashboard += "└────────────────────┴────────┴────────┴─────────────────────┘\n"
	dashboard += "\n"

	// Strengths and weaknesses
	dashboard += fmt.Sprintf("💪 Strongest Dimension: %s (%.3f)\n", sonarNames[result.StrongestDimension], result.SonarScores[result.StrongestDimension])
	dashboard += fmt.Sprintf("⚠️  Weakest Dimension: %s (%.3f)\n", sonarNames[result.WeakestDimension], result.SonarScores[result.WeakestDimension])
	dashboard += "\n"

	// Top recommendations
	dashboard += "🔧 Top Recommendations:\n"
	weakestReport := result.SonarReports[result.WeakestDimension]
	for i, rec := range weakestReport.Recommendations {
		if i >= 3 {
			break // Show top 3 only
		}
		dashboard += fmt.Sprintf("   %d. %s\n", i+1, rec)
	}
	dashboard += "\n"

	return dashboard
}

// scoreIndicator creates visual indicator for score
func (shm *SHMCalculator) scoreIndicator(score float64) string {
	if score >= 0.85 {
		return "████████" // Excellent
	} else if score >= 0.70 {
		return "██████  " // Good
	} else if score >= 0.50 {
		return "████    " // Warning
	} else {
		return "██      " // Critical
	}
}

// GetRegimeDistribution returns TSP regime allocations
func (shm *SHMCalculator) GetRegimeDistribution() map[string]float64 {
	// Three-Regime Distribution (30/20/50 from Asymmetrica methodology)
	return map[string]float64{
		"exploration":   0.30, // 30% effort on new features
		"optimization":  0.20, // 20% effort on improvements
		"stabilization": 0.50, // 50% effort on reliability
	}
}

// GetWeightOverrides allows team-specific weight customization
func (shm *SHMCalculator) GetWeightOverrides(teamID string) map[string]float64 {
	// Future enhancement: Allow teams to customize weights (50% global + 50% team override)
	// For now, return default weights
	return shm.weights
}

// WilliamsDriftDetection checks if SHM drift exceeds threshold
//
// Formula: threshold = √t × log₂(t) × 0.05
// Where t = commits since last baseline update
func (shm *SHMCalculator) WilliamsDriftDetection(currentSHM, baselineSHM float64, commitsSinceUpdate int) (bool, float64) {
	if commitsSinceUpdate <= 0 {
		commitsSinceUpdate = 1
	}

	// Williams threshold
	t := float64(commitsSinceUpdate)
	williamsThreshold := shm.williamsValue(t) * 0.05 // 5% of Williams value

	// Calculate drift
	drift := shm.abs(currentSHM - baselineSHM)
	driftPercent := (drift / baselineSHM) * 100.0

	// Auto-approve if drift < threshold
	approved := driftPercent < williamsThreshold

	return approved, driftPercent
}

// williamsValue computes √t × log₂(t)
func (shm *SHMCalculator) williamsValue(t float64) float64 {
	if t <= 0 {
		return 0.0
	}

	sqrt := shm.sqrt(t)
	log2 := shm.log2(t)

	return sqrt * log2
}

// sqrt computes square root
func (shm *SHMCalculator) sqrt(x float64) float64 {
	if x < 0 {
		return 0.0
	}
	return shm.approximateSqrt(x)
}

// approximateSqrt uses Newton's method
func (shm *SHMCalculator) approximateSqrt(x float64) float64 {
	if x == 0 {
		return 0
	}

	guess := x / 2.0
	for i := 0; i < 10; i++ {
		guess = (guess + x/guess) / 2.0
	}
	return guess
}

// log2 computes logarithm base 2
func (shm *SHMCalculator) log2(x float64) float64 {
	if x <= 0 {
		return 0.0
	}

	// log₂(x) = log(x) / log(2)
	// Simplified approximation
	result := 0.0
	value := x
	for value > 1.0 {
		value /= 2.0
		result += 1.0
	}

	return result
}

// abs computes absolute value
func (shm *SHMCalculator) abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}
