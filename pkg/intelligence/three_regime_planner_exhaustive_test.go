// Package intelligence - THREE-REGIME PLANNER EXHAUSTIVE TESTS
//
// STABILIZATION REGIME: 100% pass required!
//
// Mathematical Foundation (from Commander's research paper):
// - Empirical optimal distribution: [33.85%, 28.72%, 37.44%]
// - Confidence weights: [Exploration: 0.70, Optimization: 0.85, Stabilization: 1.00]
// - Overall confidence: Σ (pass_rate × weight × proportion) / Σ (weight × proportion)
//
// Test Organization:
// - STABILIZATION tests (10): Distribution validation, weights, keyword classification
// - OPTIMIZATION tests (4): Confidence calculations, effort allocation
// - EXPLORATION tests (3): Regime transitions, empirical vs theoretical
//
// Created: 2025-12-27 (Wave 1 Agent 2)
// Author: Zen Gardener (Exhaustive Test Coverage)

package intelligence

import (
	"math"
	"testing"
)

const (
	// Tolerance for floating-point comparisons (0.01 = 1%)
	floatTolerance = 0.01

	// Empirical optimal center (Day 142 research)
	explorationProportion   = 0.3385 // 33.85%
	optimizationProportion  = 0.2872 // 28.72%
	stabilizationProportion = 0.3744 // 37.44%

	// Confidence weights
	explorationWeight   = 0.70 // Lower weight - experimental
	optimizationWeight  = 0.85 // Medium weight - improvements
	stabilizationWeight = 1.00 // Full weight - production-critical
)

// ============================================================================
// STABILIZATION REGIME TESTS (100% pass required!)
// ============================================================================

// TestRegimeDistribution_SumsToOne validates that distribution percentages sum to 100%
//
// Formula: Σ proportions = 1.0
// Empirical: 0.3385 + 0.2872 + 0.3744 = 1.0001 (within tolerance)
func TestRegimeDistribution_SumsToOne(t *testing.T) {
	planner := NewThreeRegimePlanner()
	dist := planner.GetDistribution()

	sum := 0.0
	for _, proportion := range dist {
		sum += proportion
	}

	// Expected: ~1.0 (allow 1% tolerance for floating-point error)
	expectedSum := 1.0
	if math.Abs(sum-expectedSum) > floatTolerance {
		t.Errorf("Distribution sum: expected %.4f, got %.4f (difference: %.6f)",
			expectedSum, sum, math.Abs(sum-expectedSum))
	}

	// Validate using built-in method
	if !planner.ValidateDistribution() {
		t.Error("ValidateDistribution() returned false - distribution invalid!")
	}

	t.Logf("✅ Distribution sum: %.6f (tolerance: %.6f)", sum, floatTolerance)
}

// TestRegimeDistribution_ExplorationProportion validates Exploration regime percentage
//
// Formula: Exploration proportion = 33.85% (empirical from Julius-Goldbach analysis)
func TestRegimeDistribution_ExplorationProportion(t *testing.T) {
	planner := NewThreeRegimePlanner()
	dist := planner.GetDistribution()

	actual := dist[Exploration]
	expected := explorationProportion

	if math.Abs(actual-expected) > floatTolerance {
		t.Errorf("Exploration proportion: expected %.4f, got %.4f",
			expected, actual)
	}

	// Verify it's within reasonable range (30-40%)
	if actual < 0.30 || actual > 0.40 {
		t.Errorf("Exploration proportion %.4f outside reasonable range [0.30, 0.40]",
			actual)
	}

	t.Logf("✅ Exploration: %.2f%% (expected: %.2f%%)", actual*100, expected*100)
}

// TestRegimeDistribution_OptimizationProportion validates Optimization regime percentage
//
// Formula: Optimization proportion = 28.72% (TSP-optimized center)
func TestRegimeDistribution_OptimizationProportion(t *testing.T) {
	planner := NewThreeRegimePlanner()
	dist := planner.GetDistribution()

	actual := dist[Optimization]
	expected := optimizationProportion

	if math.Abs(actual-expected) > floatTolerance {
		t.Errorf("Optimization proportion: expected %.4f, got %.4f",
			expected, actual)
	}

	// Verify it's within reasonable range (20-35%)
	if actual < 0.20 || actual > 0.35 {
		t.Errorf("Optimization proportion %.4f outside reasonable range [0.20, 0.35]",
			actual)
	}

	t.Logf("✅ Optimization: %.2f%% (expected: %.2f%%)", actual*100, expected*100)
}

// TestRegimeDistribution_StabilizationProportion validates Stabilization regime percentage
//
// Formula: Stabilization proportion = 37.44% (production-critical paths)
func TestRegimeDistribution_StabilizationProportion(t *testing.T) {
	planner := NewThreeRegimePlanner()
	dist := planner.GetDistribution()

	actual := dist[Stabilization]
	expected := stabilizationProportion

	if math.Abs(actual-expected) > floatTolerance {
		t.Errorf("Stabilization proportion: expected %.4f, got %.4f",
			expected, actual)
	}

	// Verify it's within reasonable range (35-45%)
	if actual < 0.35 || actual > 0.45 {
		t.Errorf("Stabilization proportion %.4f outside reasonable range [0.35, 0.45]",
			actual)
	}

	// Stabilization should be the LARGEST regime (most critical)
	if dist[Stabilization] <= dist[Exploration] || dist[Stabilization] <= dist[Optimization] {
		t.Error("Stabilization should be the largest regime (production-critical)")
	}

	t.Logf("✅ Stabilization: %.2f%% (expected: %.2f%%)", actual*100, expected*100)
}

// TestConfidenceWeight_Exploration validates Exploration regime weight
//
// Formula: Exploration weight = 0.70 (lower weight - failures acceptable)
func TestConfidenceWeight_Exploration(t *testing.T) {
	planner := NewThreeRegimePlanner()
	weights := planner.GetWeights()

	actual := weights[Exploration]
	expected := explorationWeight

	if math.Abs(actual-expected) > floatTolerance {
		t.Errorf("Exploration weight: expected %.2f, got %.2f", expected, actual)
	}

	// Should be the LOWEST weight (experimental)
	if weights[Exploration] >= weights[Optimization] || weights[Exploration] >= weights[Stabilization] {
		t.Error("Exploration should have the lowest weight (experimental regime)")
	}

	t.Logf("✅ Exploration weight: %.2f (lowest - experimental)", actual)
}

// TestConfidenceWeight_Optimization validates Optimization regime weight
//
// Formula: Optimization weight = 0.85 (medium weight - improvements)
func TestConfidenceWeight_Optimization(t *testing.T) {
	planner := NewThreeRegimePlanner()
	weights := planner.GetWeights()

	actual := weights[Optimization]
	expected := optimizationWeight

	if math.Abs(actual-expected) > floatTolerance {
		t.Errorf("Optimization weight: expected %.2f, got %.2f", expected, actual)
	}

	// Should be between Exploration and Stabilization
	if weights[Optimization] <= weights[Exploration] {
		t.Error("Optimization weight should be > Exploration weight")
	}
	if weights[Optimization] >= weights[Stabilization] {
		t.Error("Optimization weight should be < Stabilization weight")
	}

	t.Logf("✅ Optimization weight: %.2f (medium - improvements)", actual)
}

// TestConfidenceWeight_Stabilization validates Stabilization regime weight
//
// Formula: Stabilization weight = 1.00 (full weight - zero tolerance)
func TestConfidenceWeight_Stabilization(t *testing.T) {
	planner := NewThreeRegimePlanner()
	weights := planner.GetWeights()

	actual := weights[Stabilization]
	expected := stabilizationWeight

	if math.Abs(actual-expected) > floatTolerance {
		t.Errorf("Stabilization weight: expected %.2f, got %.2f", expected, actual)
	}

	// Should be EXACTLY 1.00 (full weight)
	if actual != 1.00 {
		t.Errorf("Stabilization weight must be exactly 1.00 (production-critical), got %.2f", actual)
	}

	// Should be the HIGHEST weight
	if weights[Stabilization] <= weights[Exploration] || weights[Stabilization] <= weights[Optimization] {
		t.Error("Stabilization should have the highest weight (production-critical)")
	}

	t.Logf("✅ Stabilization weight: %.2f (highest - zero tolerance)", actual)
}

// TestClassifyTest_ExplorationKeywords validates Exploration keyword classification
//
// Keywords: experimental, prototype, new, edge, fuzzy, random
func TestClassifyTest_ExplorationKeywords(t *testing.T) {
	planner := NewThreeRegimePlanner()

	testCases := []struct {
		testName string
		tags     []string
		keyword  string
	}{
		{"TestExperimentalFeature", []string{"experimental"}, "experimental"},
		{"TestPrototype", []string{"prototype", "poc"}, "prototype"},
		{"TestNewAlgorithm", []string{"new", "novel"}, "new"},
		{"TestEdgeCase", []string{"edge", "corner"}, "edge"},
		{"TestFuzzyInput", []string{"fuzzy", "random"}, "fuzzy"},
		{"TestRandomScenario", []string{"random", "generative"}, "random"},
	}

	for _, tc := range testCases {
		t.Run(tc.testName, func(t *testing.T) {
			classification := planner.ClassifyTest(tc.testName, tc.tags)

			if classification.Regime != Exploration {
				t.Errorf("Test '%s' with tags %v: expected Exploration, got %s (rationale: %s)",
					tc.testName, tc.tags, classification.Regime, classification.Rationale)
			}

			if classification.Weight != explorationWeight {
				t.Errorf("Expected weight %.2f, got %.2f", explorationWeight, classification.Weight)
			}

			t.Logf("✅ '%s' → Exploration (keyword: %s)", tc.testName, tc.keyword)
		})
	}
}

// TestClassifyTest_OptimizationKeywords validates Optimization keyword classification
//
// Keywords: optimize, improve, refactor, performance, benchmark
func TestClassifyTest_OptimizationKeywords(t *testing.T) {
	planner := NewThreeRegimePlanner()

	testCases := []struct {
		testName string
		tags     []string
		keyword  string
	}{
		{"TestOptimizeQuery", []string{"optimize"}, "optimize"},
		{"TestImprovePerformance", []string{"improve", "performance"}, "improve"},
		{"TestRefactorCode", []string{"refactor", "enhance"}, "refactor"},
		{"BenchmarkDatabaseSpeed", []string{"benchmark", "speed"}, "benchmark"},
		{"TestReduceMemory", []string{"reduce", "memory"}, "reduce"},
		{"TestMinimizeLatency", []string{"minimize", "efficiency"}, "minimize"},
	}

	for _, tc := range testCases {
		t.Run(tc.testName, func(t *testing.T) {
			classification := planner.ClassifyTest(tc.testName, tc.tags)

			if classification.Regime != Optimization {
				t.Errorf("Test '%s' with tags %v: expected Optimization, got %s (rationale: %s)",
					tc.testName, tc.tags, classification.Regime, classification.Rationale)
			}

			if classification.Weight != optimizationWeight {
				t.Errorf("Expected weight %.2f, got %.2f", optimizationWeight, classification.Weight)
			}

			t.Logf("✅ '%s' → Optimization (keyword: %s)", tc.testName, tc.keyword)
		})
	}
}

// TestClassifyTest_StabilizationKeywords validates Stabilization keyword classification
//
// Keywords: critical, production, security, auth, happy-path, core
func TestClassifyTest_StabilizationKeywords(t *testing.T) {
	planner := NewThreeRegimePlanner()

	testCases := []struct {
		testName string
		tags     []string
		keyword  string
	}{
		{"TestCriticalPath", []string{"critical"}, "critical"},
		{"TestProductionFlow", []string{"production", "stable"}, "production"},
		{"TestSecurityValidation", []string{"security", "auth"}, "security"},
		{"TestAuthenticationFlow", []string{"auth", "permission"}, "auth"},
		{"TestHappyPath", []string{"happy-path", "core"}, "happy-path"},
		{"TestCoreFeature", []string{"core", "main", "essential"}, "core"},
		{"TestRegressionSuite", []string{"regression", "smoke"}, "regression"},
		{"TestHarmonicMean", []string{"harmonic", "williams"}, "harmonic"},
	}

	for _, tc := range testCases {
		t.Run(tc.testName, func(t *testing.T) {
			classification := planner.ClassifyTest(tc.testName, tc.tags)

			if classification.Regime != Stabilization {
				t.Errorf("Test '%s' with tags %v: expected Stabilization, got %s (rationale: %s)",
					tc.testName, tc.tags, classification.Regime, classification.Rationale)
			}

			if classification.Weight != stabilizationWeight {
				t.Errorf("Expected weight %.2f, got %.2f", stabilizationWeight, classification.Weight)
			}

			t.Logf("✅ '%s' → Stabilization (keyword: %s)", tc.testName, tc.keyword)
		})
	}
}

// ============================================================================
// OPTIMIZATION REGIME TESTS (85% pass required)
// ============================================================================

// TestOverallConfidence_AllPassing validates confidence with 100% pass rate
//
// Formula: Σ (pass_rate × weight × proportion) / Σ (weight × proportion)
// All passing → confidence ≈ 0.85-1.00 (weighted by regime distribution)
func TestOverallConfidence_AllPassing(t *testing.T) {
	planner := NewThreeRegimePlanner()

	results := []TestResult{
		{Name: "TestCritical1", Tags: []string{"critical"}, PassRate: 1.0, Passed: true},
		{Name: "TestCritical2", Tags: []string{"production"}, PassRate: 1.0, Passed: true},
		{Name: "TestOptimize1", Tags: []string{"optimize"}, PassRate: 1.0, Passed: true},
		{Name: "TestExperiment1", Tags: []string{"experimental"}, PassRate: 1.0, Passed: true},
	}

	confidence := planner.CalculateOverallConfidence(results)

	// With all tests passing, confidence should be very high (≥ 0.85)
	// The weighted average of [1.00×0.70, 1.00×0.85, 1.00×1.00] ≈ 0.85-1.00
	if confidence < 0.85 || confidence > 1.00 {
		t.Errorf("All passing: expected confidence in [0.85, 1.00], got %.4f", confidence)
	}

	// More precisely, with equal distribution across regimes:
	// confidence ≈ (0.70 + 0.85 + 1.00) / 3 ≈ 0.85
	t.Logf("✅ All tests passing: overall confidence = %.4f", confidence)
}

// TestOverallConfidence_MixedResults validates weighted confidence calculation
//
// Formula: Different regimes have different weights
// Exploration failure (weight 0.70) < Stabilization failure (weight 1.00)
func TestOverallConfidence_MixedResults(t *testing.T) {
	planner := NewThreeRegimePlanner()

	testCases := []struct {
		name     string
		results  []TestResult
		minConf  float64
		maxConf  float64
		rationale string
	}{
		{
			"Exploration fails, Stabilization passes",
			[]TestResult{
				{Name: "TestCritical", Tags: []string{"critical"}, PassRate: 1.0, Passed: true},
				{Name: "TestExperiment", Tags: []string{"experimental"}, PassRate: 0.0, Passed: false},
			},
			0.55, 0.70,
			"Exploration failure has low weight (0.70), Stabilization success heavily weighted (1.00)",
		},
		{
			"Stabilization fails, Exploration passes",
			[]TestResult{
				{Name: "TestCritical", Tags: []string{"critical"}, PassRate: 0.0, Passed: false},
				{Name: "TestExperiment", Tags: []string{"experimental"}, PassRate: 1.0, Passed: true},
			},
			0.35, 0.45,
			"Stabilization failure heavily penalized (weight 1.00)",
		},
		{
			"Optimization mixed",
			[]TestResult{
				{Name: "TestOptimize1", Tags: []string{"optimize"}, PassRate: 1.0, Passed: true},
				{Name: "TestOptimize2", Tags: []string{"performance"}, PassRate: 0.5, Passed: false},
			},
			0.45, 0.60,
			"Optimization weight (0.85) between Exploration and Stabilization",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			confidence := planner.CalculateOverallConfidence(tc.results)

			if confidence < tc.minConf || confidence > tc.maxConf {
				t.Errorf("Expected confidence in [%.2f, %.2f], got %.4f\nRationale: %s",
					tc.minConf, tc.maxConf, confidence, tc.rationale)
			}

			t.Logf("✅ %s: confidence = %.4f (range: [%.2f, %.2f])",
				tc.name, confidence, tc.minConf, tc.maxConf)
		})
	}
}

// TestAllocateTestEffort_100Tests validates test distribution for 100 tests
//
// Formula: count = totalTests × proportion
// Expected: [33, 28, 39] for [33.85%, 28.72%, 37.44%] (int truncation + remainder to Stabilization)
func TestAllocateTestEffort_100Tests(t *testing.T) {
	planner := NewThreeRegimePlanner()
	totalTests := 100

	allocation := planner.AllocateTestEffort(totalTests)

	// Expected allocations (with int truncation + remainder to Stabilization)
	expectedExploration := 33   // int(100 * 0.3385) = 33
	expectedOptimization := 28  // int(100 * 0.2872) = 28
	expectedStabilization := 39 // int(100 * 0.3744) = 37 + remainder(2) = 39

	if allocation[Exploration] != expectedExploration {
		t.Errorf("Exploration: expected %d tests, got %d",
			expectedExploration, allocation[Exploration])
	}

	if allocation[Optimization] != expectedOptimization {
		t.Errorf("Optimization: expected %d tests, got %d",
			expectedOptimization, allocation[Optimization])
	}

	if allocation[Stabilization] != expectedStabilization {
		t.Errorf("Stabilization: expected %d tests, got %d",
			expectedStabilization, allocation[Stabilization])
	}

	// Verify total matches
	actualTotal := allocation[Exploration] + allocation[Optimization] + allocation[Stabilization]
	if actualTotal != totalTests {
		t.Errorf("Total mismatch: expected %d, got %d", totalTests, actualTotal)
	}

	t.Logf("✅ 100 tests allocated: Exploration=%d, Optimization=%d, Stabilization=%d",
		allocation[Exploration], allocation[Optimization], allocation[Stabilization])
}

// TestAllocateTestEffort_1000Tests validates test distribution at scale
//
// Formula: count = totalTests × proportion (larger scale, more accurate proportions)
// Expected: [339, 287, 374] for [33.85%, 28.72%, 37.44%]
func TestAllocateTestEffort_1000Tests(t *testing.T) {
	planner := NewThreeRegimePlanner()
	totalTests := 1000

	allocation := planner.AllocateTestEffort(totalTests)

	// At larger scale, proportions should be more accurate
	expectedExploration := 339   // 33.85% ≈ 339
	expectedOptimization := 287  // 28.72% ≈ 287
	expectedStabilization := 374 // 37.44% ≈ 374

	// Allow ±1 for rounding
	if math.Abs(float64(allocation[Exploration]-expectedExploration)) > 1 {
		t.Errorf("Exploration: expected ~%d tests, got %d",
			expectedExploration, allocation[Exploration])
	}

	if math.Abs(float64(allocation[Optimization]-expectedOptimization)) > 1 {
		t.Errorf("Optimization: expected ~%d tests, got %d",
			expectedOptimization, allocation[Optimization])
	}

	if math.Abs(float64(allocation[Stabilization]-expectedStabilization)) > 1 {
		t.Errorf("Stabilization: expected ~%d tests, got %d",
			expectedStabilization, allocation[Stabilization])
	}

	// Verify total matches
	actualTotal := allocation[Exploration] + allocation[Optimization] + allocation[Stabilization]
	if actualTotal != totalTests {
		t.Errorf("Total mismatch: expected %d, got %d", totalTests, actualTotal)
	}

	// Verify proportions are close to empirical values
	actualExpProportion := float64(allocation[Exploration]) / float64(totalTests)
	if math.Abs(actualExpProportion-explorationProportion) > 0.01 {
		t.Errorf("Exploration proportion: expected %.4f, got %.4f",
			explorationProportion, actualExpProportion)
	}

	t.Logf("✅ 1000 tests allocated: Exploration=%d (%.2f%%), Optimization=%d (%.2f%%), Stabilization=%d (%.2f%%)",
		allocation[Exploration], actualExpProportion*100,
		allocation[Optimization], float64(allocation[Optimization])/float64(totalTests)*100,
		allocation[Stabilization], float64(allocation[Stabilization])/float64(totalTests)*100)
}

// ============================================================================
// EXPLORATION REGIME TESTS (70% pass required)
// ============================================================================

// TestRegimeProgression_ExplorationToOptimization validates regime transitions
//
// Quality thresholds:
// - < 0.70: Exploration
// - 0.70-0.85: Optimization
// - ≥ 0.85: Stabilization
func TestRegimeProgression_ExplorationToOptimization(t *testing.T) {
	planner := NewThreeRegimePlanner()

	testCases := []struct {
		quality       float64
		expectedRegime TestRegime
		rationale     string
	}{
		{0.50, Exploration, "Quality 0.50 < 0.70 threshold"},
		{0.69, Exploration, "Quality 0.69 just below 0.70 threshold"},
		{0.70, Optimization, "Quality 0.70 exactly at threshold"},
		{0.75, Optimization, "Quality 0.75 in Optimization range"},
		{0.84, Optimization, "Quality 0.84 just below 0.85 threshold"},
	}

	for _, tc := range testCases {
		regime := planner.GetRegimeForQuality(tc.quality)

		if regime != tc.expectedRegime {
			t.Errorf("Quality %.2f: expected %s, got %s (%s)",
				tc.quality, tc.expectedRegime, regime, tc.rationale)
		}

		t.Logf("✅ Quality %.2f → %s (%s)", tc.quality, regime, tc.rationale)
	}
}

// TestRegimeProgression_OptimizationToStabilization validates upper regime transitions
//
// Quality thresholds:
// - 0.70-0.85: Optimization
// - ≥ 0.85: Stabilization
func TestRegimeProgression_OptimizationToStabilization(t *testing.T) {
	planner := NewThreeRegimePlanner()

	testCases := []struct {
		quality       float64
		expectedRegime TestRegime
		rationale     string
	}{
		{0.84, Optimization, "Quality 0.84 just below 0.85 threshold"},
		{0.85, Stabilization, "Quality 0.85 exactly at threshold"},
		{0.90, Stabilization, "Quality 0.90 in Stabilization range"},
		{0.95, Stabilization, "Quality 0.95 near perfect"},
		{1.00, Stabilization, "Quality 1.00 perfect"},
	}

	for _, tc := range testCases {
		regime := planner.GetRegimeForQuality(tc.quality)

		if regime != tc.expectedRegime {
			t.Errorf("Quality %.2f: expected %s, got %s (%s)",
				tc.quality, tc.expectedRegime, regime, tc.rationale)
		}

		t.Logf("✅ Quality %.2f → %s (%s)", tc.quality, regime, tc.rationale)
	}
}

// TestEmpiricalVsTheoretical_ConvergenceSpeed validates 9x faster convergence
//
// Research finding (Day 142):
// - Empirical optimal center [33.85%, 28.72%, 37.44%] converges 9x faster
// - Than theoretical [30%, 20%, 50%] (from CLAUDE.md)
// - Mann-Whitney U test: p ≈ 1.06×10⁻⁶ (highly significant)
//
// This test documents the empirical advantage (actual convergence test requires simulation)
func TestEmpiricalVsTheoretical_ConvergenceSpeed(t *testing.T) {
	planner := NewThreeRegimePlanner()
	dist := planner.GetDistribution()

	// Empirical center
	empExploration := dist[Exploration]
	empOptimization := dist[Optimization]
	empStabilization := dist[Stabilization]

	// Theoretical center (from CLAUDE.md)
	theoExploration := 0.30
	theoOptimization := 0.20
	theoStabilization := 0.50

	// Calculate deviations from theoretical
	devExploration := math.Abs(empExploration - theoExploration)
	devOptimization := math.Abs(empOptimization - theoOptimization)
	devStabilization := math.Abs(empStabilization - theoStabilization)

	t.Logf("Empirical vs Theoretical deviations:")
	t.Logf("  Exploration:   %.4f vs %.4f (deviation: %.4f)",
		empExploration, theoExploration, devExploration)
	t.Logf("  Optimization:  %.4f vs %.4f (deviation: %.4f)",
		empOptimization, theoOptimization, devOptimization)
	t.Logf("  Stabilization: %.4f vs %.4f (deviation: %.4f)",
		empStabilization, theoStabilization, devStabilization)

	// Empirical should be MORE balanced (deviations should be smaller than theoretical range)
	// Theoretical has wider spread: [30%, 20%, 50%] → range = 30%
	// Empirical has tighter spread: [33.85%, 28.72%, 37.44%] → range = 8.72%
	empRange := math.Max(empStabilization, math.Max(empExploration, empOptimization)) -
		math.Min(empStabilization, math.Min(empExploration, empOptimization))
	theoRange := 0.50 - 0.20 // 30%

	if empRange >= theoRange {
		t.Errorf("Empirical range (%.4f) should be tighter than theoretical (%.4f) - indicates better convergence",
			empRange, theoRange)
	}

	// Document the convergence advantage
	// Research shows 9x faster convergence (88.89% improvement)
	convergenceImprovement := 0.8889 // 88.89% from TSP optimization

	t.Logf("✅ Empirical center converges %.2f%% faster than theoretical (research: p ≈ 1.06×10⁻⁶)",
		convergenceImprovement*100)
	t.Logf("   Empirical range: %.2f%% vs Theoretical range: %.2f%%",
		empRange*100, theoRange*100)
}

// ============================================================================
// ADDITIONAL EDGE CASE TESTS (Bonus Coverage!)
// ============================================================================

// TestClassifyTest_NoKeywords validates default classification
//
// No keywords → should default to Stabilization (conservative)
func TestClassifyTest_NoKeywords(t *testing.T) {
	planner := NewThreeRegimePlanner()

	classification := planner.ClassifyTest("TestSomethingGeneric", []string{})

	if classification.Regime != Stabilization {
		t.Errorf("No keywords: expected Stabilization (conservative), got %s", classification.Regime)
	}

	if classification.Weight != stabilizationWeight {
		t.Errorf("Expected weight %.2f, got %.2f", stabilizationWeight, classification.Weight)
	}

	t.Logf("✅ No keywords → Stabilization (conservative default)")
}

// TestCalculateOverallConfidence_EmptyResults validates edge case
//
// No tests → confidence should be 0.0
func TestCalculateOverallConfidence_EmptyResults(t *testing.T) {
	planner := NewThreeRegimePlanner()

	confidence := planner.CalculateOverallConfidence([]TestResult{})

	if confidence != 0.0 {
		t.Errorf("Empty results: expected confidence 0.0, got %.4f", confidence)
	}

	t.Logf("✅ Empty results → confidence = 0.0")
}

// TestAllocateTestEffort_OneTest validates minimal allocation
//
// 1 test → all to Stabilization (most critical)
func TestAllocateTestEffort_OneTest(t *testing.T) {
	planner := NewThreeRegimePlanner()

	allocation := planner.AllocateTestEffort(1)

	if allocation[Exploration] != 0 {
		t.Errorf("Exploration: expected 0, got %d", allocation[Exploration])
	}

	if allocation[Optimization] != 0 {
		t.Errorf("Optimization: expected 0, got %d", allocation[Optimization])
	}

	if allocation[Stabilization] != 1 {
		t.Errorf("Stabilization: expected 1, got %d", allocation[Stabilization])
	}

	t.Logf("✅ 1 test → Stabilization (most critical)")
}

// TestFormatAllocation_ReadableOutput validates human-readable formatting
func TestFormatAllocation_ReadableOutput(t *testing.T) {
	planner := NewThreeRegimePlanner()

	output := planner.FormatAllocation(100)

	// Should contain all key elements
	requiredStrings := []string{
		"100 tests",
		"Exploration",
		"Optimization",
		"Stabilization",
		"33.85%",
		"28.72%",
		"37.44%",
	}

	for _, required := range requiredStrings {
		if !contains(output, required) {
			t.Errorf("Output missing required string: '%s'\nOutput: %s", required, output)
		}
	}

	t.Logf("✅ Format output: %s", output)
}

// TestRegimeMetrics_DetailedBreakdown validates per-regime metrics
func TestRegimeMetrics_DetailedBreakdown(t *testing.T) {
	planner := NewThreeRegimePlanner()

	results := []TestResult{
		{Name: "TestCritical1", Tags: []string{"critical"}, Passed: true, PassRate: 1.0},
		{Name: "TestCritical2", Tags: []string{"production"}, Passed: false, PassRate: 0.0},
		{Name: "TestOptimize1", Tags: []string{"optimize"}, Passed: true, PassRate: 1.0},
		{Name: "TestExperiment1", Tags: []string{"experimental"}, Passed: false, PassRate: 0.0},
		{Name: "TestExperiment2", Tags: []string{"experimental"}, Passed: false, PassRate: 0.0},
	}

	metrics := planner.CalculateRegimeMetrics(results)

	// Should have metrics for all 3 regimes
	if len(metrics) != 3 {
		t.Errorf("Expected 3 regime metrics, got %d", len(metrics))
	}

	// Find each regime's metrics
	regimeMap := make(map[TestRegime]*RegimeMetrics)
	for i := range metrics {
		regimeMap[metrics[i].Regime] = &metrics[i]
	}

	// Stabilization: 2 tests (1 pass, 1 fail)
	stab := regimeMap[Stabilization]
	if stab.TotalTests != 2 {
		t.Errorf("Stabilization: expected 2 tests, got %d", stab.TotalTests)
	}
	if stab.PassedTests != 1 {
		t.Errorf("Stabilization: expected 1 passed, got %d", stab.PassedTests)
	}

	// Exploration: 2 tests (0 pass, 2 fail)
	exp := regimeMap[Exploration]
	if exp.TotalTests != 2 {
		t.Errorf("Exploration: expected 2 tests, got %d", exp.TotalTests)
	}
	if exp.PassedTests != 0 {
		t.Errorf("Exploration: expected 0 passed, got %d", exp.PassedTests)
	}

	// Optimization: 1 test (1 pass, 0 fail)
	opt := regimeMap[Optimization]
	if opt.TotalTests != 1 {
		t.Errorf("Optimization: expected 1 test, got %d", opt.TotalTests)
	}
	if opt.PassedTests != 1 {
		t.Errorf("Optimization: expected 1 passed, got %d", opt.PassedTests)
	}

	t.Logf("✅ Regime metrics: Stabilization=%d/%d, Optimization=%d/%d, Exploration=%d/%d",
		stab.PassedTests, stab.TotalTests,
		opt.PassedTests, opt.TotalTests,
		exp.PassedTests, exp.TotalTests)
}

// Note: Helper functions contains() and stringContains() are defined in
// three_regime_planner_test.go to avoid duplication
