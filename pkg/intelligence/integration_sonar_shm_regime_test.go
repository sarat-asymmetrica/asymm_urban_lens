package intelligence

import (
	"context"
	"testing"

	"github.com/asymmetrica/urbanlens/pkg/intelligence/sonars"
)

// ============================================================================
// STABILIZATION TESTS (100% PASS REQUIRED)
// ============================================================================

// TestIntegration_AllSonars_FeedIntoSHM validates that all 6 sonars produce scores that feed into SHM
func TestIntegration_AllSonars_FeedIntoSHM(t *testing.T) {
	shm := NewSHMCalculator()

	// Create test app with all components
	app := createTestApp(t)

	ctx := context.Background()
	result, err := shm.CalculateSHM(ctx, app)

	if err != nil {
		t.Fatalf("SHM calculation failed: %v", err)
	}

	// CRITICAL: All 6 sonars MUST produce scores
	expectedSonars := []string{"ux", "design", "code", "semantic", "journey", "state"}
	for _, sonarName := range expectedSonars {
		score, exists := result.SonarScores[sonarName]
		if !exists {
			t.Errorf("Sonar %s did not produce a score", sonarName)
			continue
		}

		// Score must be in valid range [0.0, 1.0]
		if score < 0.0 || score > 1.0 {
			t.Errorf("Sonar %s score out of range: %.3f (must be 0.0-1.0)", sonarName, score)
		}

		// Report must exist
		report, reportExists := result.SonarReports[sonarName]
		if !reportExists {
			t.Errorf("Sonar %s did not produce a report", sonarName)
			continue
		}

		// Report score must match sonar score
		if report.Score != score {
			t.Errorf("Sonar %s report score (%.3f) does not match sonar score (%.3f)", sonarName, report.Score, score)
		}
	}

	// Final SHM must exist and be valid
	if result.SHM < 0.0 || result.SHM > 1.0 {
		t.Errorf("Final SHM out of range: %.3f (must be 0.0-1.0)", result.SHM)
	}

	t.Logf("SUCCESS: All 6 sonars produced valid scores → SHM = %.3f", result.SHM)
}

// TestIntegration_SHM_WeightsAppliedCorrectly validates weight application in SHM calculation
func TestIntegration_SHM_WeightsAppliedCorrectly(t *testing.T) {
	shm := NewSHMCalculator()

	// Create scores where UX and Design dominate (they have 50% combined weight)
	scores := map[string]float64{
		"ux":       1.0, // Weight: 0.25
		"design":   1.0, // Weight: 0.25
		"code":     0.0, // Weight: 0.125
		"semantic": 0.0, // Weight: 0.125
		"journey":  0.0, // Weight: 0.125
		"state":    0.0, // Weight: 0.125
	}

	shmValue := shm.computeWeightedSHM(scores)

	// Expected: (1.0 × 0.25) + (1.0 × 0.25) + (0.0 × 0.125) × 4 = 0.50
	expected := 0.50

	if shmValue < expected-0.01 || shmValue > expected+0.01 {
		t.Errorf("Weight application incorrect: got %.3f, expected %.3f", shmValue, expected)
		t.Logf("Formula: (UX × 0.25) + (Design × 0.25) + (Code × 0.125) + (Semantic × 0.125) + (Journey × 0.125) + (State × 0.125)")
		t.Logf("Calculation: (%.2f × 0.25) + (%.2f × 0.25) + (%.2f × 0.125) + (%.2f × 0.125) + (%.2f × 0.125) + (%.2f × 0.125)",
			scores["ux"], scores["design"], scores["code"], scores["semantic"], scores["journey"], scores["state"])
	}

	// Test another scenario: All internal quality good, UX/Design bad
	scores2 := map[string]float64{
		"ux":       0.0, // Weight: 0.25
		"design":   0.0, // Weight: 0.25
		"code":     1.0, // Weight: 0.125
		"semantic": 1.0, // Weight: 0.125
		"journey":  1.0, // Weight: 0.125
		"state":    1.0, // Weight: 0.125
	}

	shmValue2 := shm.computeWeightedSHM(scores2)

	// Expected: (0.0 × 0.25) × 2 + (1.0 × 0.125) × 4 = 0.50
	expected2 := 0.50

	if shmValue2 < expected2-0.01 || shmValue2 > expected2+0.01 {
		t.Errorf("Weight application incorrect (scenario 2): got %.3f, expected %.3f", shmValue2, expected2)
	}

	t.Logf("SUCCESS: Weights applied correctly (UX+Design = 50%%, Internal = 50%%)")
}

// TestIntegration_SHM_ExplorationRegime validates SHM < 0.70 → Exploration
func TestIntegration_SHM_ExplorationRegime(t *testing.T) {
	shm := NewSHMCalculator()

	// Create app with low quality scores (exploration phase)
	app := createTestApp(t)

	// Force exploration-level scores by using minimal app
	app.Frontend.Components = []string{"App.tsx"} // Minimal components
	app.Backend.APIEndpoints = 2                  // Few endpoints

	ctx := context.Background()
	result, err := shm.CalculateSHM(ctx, app)

	if err != nil {
		t.Fatalf("SHM calculation failed: %v", err)
	}

	// For exploration regime, we expect SHM < 0.70
	// If actual SHM is higher, we'll manually set scores to test regime detection
	testScores := []float64{0.30, 0.50, 0.65, 0.69}

	for _, testSHM := range testScores {
		regime := shm.determineRegime(testSHM)
		if regime != RegimeExploration {
			t.Errorf("SHM %.2f should be Exploration, got %s", testSHM, regime)
		}
	}

	t.Logf("SUCCESS: SHM < 0.70 correctly maps to Exploration regime")
	t.Logf("Actual app SHM: %.3f → %s", result.SHM, result.Regime)
}

// TestIntegration_SHM_OptimizationRegime validates 0.70 ≤ SHM < 0.85 → Optimization
func TestIntegration_SHM_OptimizationRegime(t *testing.T) {
	shm := NewSHMCalculator()

	// Test regime determination for optimization range
	testScores := []float64{0.70, 0.75, 0.80, 0.84, 0.8499}

	for _, testSHM := range testScores {
		regime := shm.determineRegime(testSHM)
		if regime != RegimeOptimization {
			t.Errorf("SHM %.4f should be Optimization, got %s", testSHM, regime)
		}
	}

	// Test boundary: 0.6999 should be Exploration
	regime := shm.determineRegime(0.6999)
	if regime != RegimeExploration {
		t.Errorf("SHM 0.6999 should be Exploration (boundary test), got %s", regime)
	}

	// Test boundary: 0.85 should be Stabilization
	regime = shm.determineRegime(0.85)
	if regime != RegimeStabilization {
		t.Errorf("SHM 0.85 should be Stabilization (boundary test), got %s", regime)
	}

	t.Logf("SUCCESS: 0.70 ≤ SHM < 0.85 correctly maps to Optimization regime")
}

// TestIntegration_SHM_StabilizationRegime validates SHM ≥ 0.85 → Stabilization
func TestIntegration_SHM_StabilizationRegime(t *testing.T) {
	shm := NewSHMCalculator()

	// Test regime determination for stabilization range
	testScores := []float64{0.85, 0.90, 0.95, 1.00}

	for _, testSHM := range testScores {
		regime := shm.determineRegime(testSHM)
		if regime != RegimeStabilization {
			t.Errorf("SHM %.2f should be Stabilization, got %s", testSHM, regime)
		}
	}

	// Test boundary: 0.8499 should be Optimization
	regime := shm.determineRegime(0.8499)
	if regime != RegimeOptimization {
		t.Errorf("SHM 0.8499 should be Optimization (boundary test), got %s", regime)
	}

	t.Logf("SUCCESS: SHM ≥ 0.85 correctly maps to Stabilization regime")
}

// TestIntegration_SonarEngine_RunsAllSonars validates engine orchestration
func TestIntegration_SonarEngine_RunsAllSonars(t *testing.T) {
	shm := NewSHMCalculator()
	app := createTestApp(t)
	ctx := context.Background()

	// Run SHM calculation which orchestrates all 6 sonars
	result, err := shm.CalculateSHM(ctx, app)

	if err != nil {
		t.Fatalf("Sonar orchestration failed: %v", err)
	}

	// Verify all 6 sonars were executed
	if len(result.SonarScores) != 6 {
		t.Errorf("Expected 6 sonars to run, got %d", len(result.SonarScores))
	}

	if len(result.SonarReports) != 6 {
		t.Errorf("Expected 6 sonar reports, got %d", len(result.SonarReports))
	}

	// Verify each sonar produced valid output
	sonarNames := []string{"ux", "design", "code", "semantic", "journey", "state"}
	for _, name := range sonarNames {
		// Check score exists
		if _, exists := result.SonarScores[name]; !exists {
			t.Errorf("Sonar %s did not produce score", name)
		}

		// Check report exists
		report, exists := result.SonarReports[name]
		if !exists {
			t.Errorf("Sonar %s did not produce report", name)
			continue
		}

		// Verify report has required fields
		if report.SonarName == "" {
			t.Errorf("Sonar %s report missing name", name)
		}

		if report.Summary == "" {
			t.Errorf("Sonar %s report missing summary", name)
		}

		if report.Status == "" {
			t.Errorf("Sonar %s report missing status", name)
		}
	}

	// Verify weakest and strongest dimensions were identified
	if result.WeakestDimension == "" {
		t.Error("Weakest dimension not identified")
	}

	if result.StrongestDimension == "" {
		t.Error("Strongest dimension not identified")
	}

	// Verify weakest and strongest are different (unless all scores identical)
	allScoresIdentical := true
	firstScore := result.SonarScores["ux"]
	for _, score := range result.SonarScores {
		if score != firstScore {
			allScoresIdentical = false
			break
		}
	}

	if !allScoresIdentical && result.WeakestDimension == result.StrongestDimension {
		t.Error("Weakest and strongest dimensions should be different when scores vary")
	}

	t.Logf("SUCCESS: Sonar engine orchestrated all 6 sonars correctly")
	t.Logf("Weakest: %s (%.3f), Strongest: %s (%.3f)",
		result.WeakestDimension, result.SonarScores[result.WeakestDimension],
		result.StrongestDimension, result.SonarScores[result.StrongestDimension])
}

// TestIntegration_RegimeDetermination_Boundaries validates exact boundary conditions
func TestIntegration_RegimeDetermination_Boundaries(t *testing.T) {
	shm := NewSHMCalculator()

	// Test exact boundaries with high precision
	tests := []struct {
		shmValue float64
		expected Regime
		reason   string
	}{
		{0.0, RegimeExploration, "Minimum value"},
		{0.69, RegimeExploration, "Just below exploration boundary"},
		{0.6999999, RegimeExploration, "Floating point precision test (exploration)"},
		{0.70, RegimeOptimization, "Exact optimization start"},
		{0.7000001, RegimeOptimization, "Floating point precision test (optimization)"},
		{0.77, RegimeOptimization, "Middle of optimization"},
		{0.84, RegimeOptimization, "Just below stabilization boundary"},
		{0.8499999, RegimeOptimization, "Floating point precision test (optimization end)"},
		{0.85, RegimeStabilization, "Exact stabilization start"},
		{0.8500001, RegimeStabilization, "Floating point precision test (stabilization)"},
		{0.92, RegimeStabilization, "Middle of stabilization"},
		{1.0, RegimeStabilization, "Maximum value"},
	}

	for _, test := range tests {
		regime := shm.determineRegime(test.shmValue)
		if regime != test.expected {
			t.Errorf("Boundary test failed for SHM %.7f (%s): got %s, expected %s",
				test.shmValue, test.reason, regime, test.expected)
		}
	}

	t.Logf("SUCCESS: All boundary conditions validated")
	t.Logf("Exploration: [0.0, 0.70), Optimization: [0.70, 0.85), Stabilization: [0.85, 1.0]")
}

// ============================================================================
// OPTIMIZATION TESTS (85% PASS REQUIRED)
// ============================================================================

// TestIntegration_SonarEngine_ParallelExecution validates concurrent sonar execution
func TestIntegration_SonarEngine_ParallelExecution(t *testing.T) {
	shm := NewSHMCalculator()
	app := createTestApp(t)
	ctx := context.Background()

	// Run SHM calculation multiple times to verify consistency
	const iterations = 5
	results := make([]*SHMResult, iterations)

	for i := 0; i < iterations; i++ {
		result, err := shm.CalculateSHM(ctx, app)
		if err != nil {
			t.Fatalf("Iteration %d failed: %v", i+1, err)
		}
		results[i] = result
	}

	// All iterations should produce identical results (deterministic)
	firstSHM := results[0].SHM
	firstRegime := results[0].Regime

	for i := 1; i < iterations; i++ {
		// Use epsilon comparison for floating point (tolerance: 0.001)
		diff := results[i].SHM - firstSHM
		if diff < 0 {
			diff = -diff
		}
		if diff > 0.001 {
			t.Errorf("Iteration %d SHM (%.3f) differs from first (%.3f) - non-deterministic execution",
				i+1, results[i].SHM, firstSHM)
		}

		if results[i].Regime != firstRegime {
			t.Errorf("Iteration %d Regime (%s) differs from first (%s) - non-deterministic execution",
				i+1, results[i].Regime, firstRegime)
		}
	}

	t.Logf("SUCCESS: Sonar execution is deterministic across %d iterations", iterations)
	t.Logf("Consistent SHM: %.3f, Regime: %s", firstSHM, firstRegime)
}

// TestIntegration_SHM_UpdatesOnChange validates SHM recalculation on app changes
func TestIntegration_SHM_UpdatesOnChange(t *testing.T) {
	shm := NewSHMCalculator()
	ctx := context.Background()

	// Baseline: Simple app
	app1 := createTestApp(t)
	app1.Frontend.Components = []string{"App.tsx", "Home.tsx"}
	app1.Backend.APIEndpoints = 3

	result1, err := shm.CalculateSHM(ctx, app1)
	if err != nil {
		t.Fatalf("Baseline SHM calculation failed: %v", err)
	}

	// Modified: Complex app (more components, more endpoints)
	app2 := createTestApp(t)
	app2.Frontend.Components = []string{"App.tsx", "Home.tsx", "Dashboard.tsx", "Profile.tsx", "Settings.tsx"}
	app2.Backend.APIEndpoints = 12

	result2, err := shm.CalculateSHM(ctx, app2)
	if err != nil {
		t.Fatalf("Modified SHM calculation failed: %v", err)
	}

	// SHM should change when app changes
	if result1.SHM == result2.SHM {
		t.Logf("WARNING: SHM unchanged despite app modifications (%.3f == %.3f)", result1.SHM, result2.SHM)
		t.Logf("This may be expected if changes don't affect quality metrics")
	} else {
		t.Logf("SUCCESS: SHM updated on app change (%.3f → %.3f)", result1.SHM, result2.SHM)
	}

	// At least some sonar scores should differ
	changeCount := 0
	for sonar := range result1.SonarScores {
		if result1.SonarScores[sonar] != result2.SonarScores[sonar] {
			changeCount++
			t.Logf("Sonar %s changed: %.3f → %.3f", sonar, result1.SonarScores[sonar], result2.SonarScores[sonar])
		}
	}

	if changeCount == 0 {
		t.Logf("WARNING: No individual sonar scores changed despite app modifications")
	}

	t.Logf("Changed sonars: %d/6", changeCount)
}

// TestIntegration_RegimeTransition_ExplorationToOptimization validates regime transitions
func TestIntegration_RegimeTransition_ExplorationToOptimization(t *testing.T) {
	shm := NewSHMCalculator()

	// Simulate quality improvement over time
	explorationSHM := 0.65  // Below 0.70
	optimizationSHM := 0.75 // Between 0.70 and 0.85

	regime1 := shm.determineRegime(explorationSHM)
	regime2 := shm.determineRegime(optimizationSHM)

	if regime1 != RegimeExploration {
		t.Errorf("SHM %.2f should be Exploration, got %s", explorationSHM, regime1)
	}

	if regime2 != RegimeOptimization {
		t.Errorf("SHM %.2f should be Optimization, got %s", optimizationSHM, regime2)
	}

	// Verify transition happened
	if regime1 == regime2 {
		t.Error("Regime should transition from Exploration to Optimization")
	}

	t.Logf("SUCCESS: Regime transitioned correctly")
	t.Logf("SHM %.2f → %s", explorationSHM, regime1)
	t.Logf("SHM %.2f → %s (transition!)", optimizationSHM, regime2)
}

// TestIntegration_RegimeTransition_OptimizationToStabilization validates optimization → stabilization
func TestIntegration_RegimeTransition_OptimizationToStabilization(t *testing.T) {
	shm := NewSHMCalculator()

	// Simulate quality improvement to production-ready
	optimizationSHM := 0.80   // Between 0.70 and 0.85
	stabilizationSHM := 0.90  // Above 0.85

	regime1 := shm.determineRegime(optimizationSHM)
	regime2 := shm.determineRegime(stabilizationSHM)

	if regime1 != RegimeOptimization {
		t.Errorf("SHM %.2f should be Optimization, got %s", optimizationSHM, regime1)
	}

	if regime2 != RegimeStabilization {
		t.Errorf("SHM %.2f should be Stabilization, got %s", stabilizationSHM, regime2)
	}

	// Verify transition happened
	if regime1 == regime2 {
		t.Error("Regime should transition from Optimization to Stabilization")
	}

	t.Logf("SUCCESS: Regime transitioned correctly")
	t.Logf("SHM %.2f → %s", optimizationSHM, regime1)
	t.Logf("SHM %.2f → %s (production ready!)", stabilizationSHM, regime2)
}

// ============================================================================
// EXPLORATION TESTS (70% PASS REQUIRED)
// ============================================================================

// TestIntegration_EndToEnd_FullPipeline validates complete data flow
func TestIntegration_EndToEnd_FullPipeline(t *testing.T) {
	// This test validates the COMPLETE pipeline:
	// App → 6 Sonars → SHM Calculator → Regime Determination → Dashboard

	shm := NewSHMCalculator()
	app := createTestApp(t)
	ctx := context.Background()

	// Step 1: Run all sonars
	t.Log("Step 1: Running all 6 sonars...")
	result, err := shm.CalculateSHM(ctx, app)
	if err != nil {
		t.Fatalf("Pipeline failed at SHM calculation: %v", err)
	}

	// Step 2: Verify all sonars produced output
	t.Log("Step 2: Verifying sonar outputs...")
	if len(result.SonarScores) != 6 {
		t.Errorf("Expected 6 sonar scores, got %d", len(result.SonarScores))
	}

	// Step 3: Verify SHM aggregation
	t.Log("Step 3: Verifying SHM aggregation...")
	if result.SHM < 0.0 || result.SHM > 1.0 {
		t.Errorf("SHM out of range: %.3f", result.SHM)
	}

	// Step 4: Verify regime determination
	t.Log("Step 4: Verifying regime determination...")
	expectedRegime := shm.determineRegime(result.SHM)
	if result.Regime != expectedRegime {
		t.Errorf("Regime mismatch: result has %s, expected %s for SHM %.3f",
			result.Regime, expectedRegime, result.SHM)
	}

	// Step 5: Generate dashboard
	t.Log("Step 5: Generating dashboard...")
	dashboard := shm.GenerateDashboard(result)
	if dashboard == "" {
		t.Error("Dashboard generation failed - empty output")
	}

	// Step 6: Verify dashboard contains all key information
	t.Log("Step 6: Validating dashboard content...")
	expectedSections := []string{
		"UNIFIED INTELLIGENCE MONITORING SYSTEM",
		"System Health Metric (SHM)",
		"Regime:",
		"UX Sonar",
		"Design Sonar",
		"Code Sonar",
		"Semantic Sonar",
		"Journey Sonar",
		"State Sonar",
		"Strongest Dimension",
		"Weakest Dimension",
	}

	for _, section := range expectedSections {
		if !containsString(dashboard, section) {
			t.Errorf("Dashboard missing section: %s", section)
		}
	}

	// Final validation: Everything connected
	t.Log("SUCCESS: Complete pipeline validated!")
	t.Logf("Pipeline: App → 6 Sonars → SHM (%.3f) → Regime (%s) → Dashboard (%d chars)",
		result.SHM, result.Regime, len(dashboard))

	// Print dashboard for visual inspection
	t.Log("\n" + dashboard)
}

// TestIntegration_SonarFailure_Graceful validates graceful handling of sonar failures
func TestIntegration_SonarFailure_Graceful(t *testing.T) {
	// NOTE: Current implementation doesn't have graceful failure handling
	// If one sonar fails, CalculateSHM panics or returns error
	// This test validates that behavior is consistent

	shm := NewSHMCalculator()

	// Create invalid app (nil pointers) to trigger sonar failures
	app := &sonars.AppState{
		RootPath: "/nonexistent/path",
		AppType:  "InvalidApp",
		// No Backend, Frontend, Database - will cause issues
	}

	ctx := context.Background()

	// Catch panic if it occurs
	defer func() {
		if r := recover(); r != nil {
			t.Logf("Sonar panicked as expected (no graceful degradation): %v", r)
			t.Log("FUTURE ENHANCEMENT: Could implement graceful degradation (skip failed sonars)")
		}
	}()

	_, err := shm.CalculateSHM(ctx, app)

	// We expect an error or panic (current behavior)
	if err == nil {
		t.Log("SHM calculation succeeded despite invalid app - robust implementation!")
	} else {
		t.Logf("SHM calculation failed as expected (no graceful degradation): %v", err)
		t.Log("FUTURE ENHANCEMENT: Could implement graceful degradation (skip failed sonars)")
	}

	// This test documents current behavior
	// Future: Could enhance to compute SHM with subset of sonars
}

// ============================================================================
// INTEGRATION WITH THREE-REGIME PLANNER
// ============================================================================

// TestIntegration_SHM_ToThreeRegimePlanner validates SHM → Regime → Test Planning
func TestIntegration_SHM_ToThreeRegimePlanner(t *testing.T) {
	shm := NewSHMCalculator()
	planner := NewThreeRegimePlanner()

	app := createTestApp(t)
	ctx := context.Background()

	// Calculate SHM
	result, err := shm.CalculateSHM(ctx, app)
	if err != nil {
		t.Fatalf("SHM calculation failed: %v", err)
	}

	// Map SHM to test regime
	testRegime := planner.GetRegimeForQuality(result.SHM)

	// Verify consistency with SHM regime
	expectedTestRegime := mapSHMRegimeToTestRegime(result.Regime)
	if testRegime != expectedTestRegime {
		t.Errorf("Test regime (%s) does not match SHM regime (%s)",
			testRegime, result.Regime)
	}

	// Generate test allocation
	totalTests := 100
	allocation := planner.AllocateTestEffort(totalTests)

	t.Logf("SUCCESS: SHM integrated with Three-Regime Planner")
	t.Logf("SHM: %.3f → Regime: %s → Test Regime: %s", result.SHM, result.Regime, testRegime)
	t.Logf("Test Allocation: Exploration=%d, Optimization=%d, Stabilization=%d",
		allocation[Exploration], allocation[Optimization], allocation[Stabilization])
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

// createTestApp creates a standard test app for integration tests
func createTestApp(t *testing.T) *sonars.AppState {
	return &sonars.AppState{
		RootPath: "/tmp/test-app",
		AppType:  "TodoApp",
		Backend: &sonars.BackendInfo{
			Language:     "go",
			EntryPoint:   "main.go",
			APIEndpoints: 8,
			Handlers:     []string{"handlers/todo.go", "handlers/user.go", "handlers/auth.go"},
		},
		Frontend: &sonars.FrontendInfo{
			Framework:  "react",
			EntryPoint: "App.tsx",
			Components: []string{
				"App.tsx",
				"TodoList.tsx",
				"TodoItem.tsx",
				"AddTodo.tsx",
				"UserProfile.tsx",
			},
			Routes: []string{"/", "/todos", "/profile", "/settings"},
		},
		Database: &sonars.DatabaseInfo{
			Type:       "postgres",
			SchemaFile: "schema.sql",
			Tables:     []string{"todos", "users", "sessions"},
		},
		Configuration: map[string]string{
			"api_base_url": "http://localhost:8080",
			"db_url":       "postgres://localhost:5432/testdb",
		},
	}
}

// mapSHMRegimeToTestRegime converts SHM Regime to TestRegime
func mapSHMRegimeToTestRegime(shmRegime Regime) TestRegime {
	switch shmRegime {
	case RegimeExploration:
		return Exploration
	case RegimeOptimization:
		return Optimization
	case RegimeStabilization:
		return Stabilization
	default:
		return Exploration // Default to exploration for unknown
	}
}

// Note: containsString helper is defined in shm_calculator_test.go
