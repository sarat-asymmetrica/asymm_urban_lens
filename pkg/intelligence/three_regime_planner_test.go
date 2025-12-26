package intelligence

import (
	"math"
	"testing"
)

// TestNewThreeRegimePlanner validates planner initialization
func TestNewThreeRegimePlanner(t *testing.T) {
	planner := NewThreeRegimePlanner()

	if planner == nil {
		t.Fatal("NewThreeRegimePlanner returned nil")
	}

	// Validate empirical distribution
	if planner.distribution[Exploration] != 0.3385 {
		t.Errorf("Expected Exploration=0.3385, got %.4f", planner.distribution[Exploration])
	}

	if planner.distribution[Optimization] != 0.2872 {
		t.Errorf("Expected Optimization=0.2872, got %.4f", planner.distribution[Optimization])
	}

	if planner.distribution[Stabilization] != 0.3744 {
		t.Errorf("Expected Stabilization=0.3744, got %.4f", planner.distribution[Stabilization])
	}

	// Validate weights
	if planner.weights[Exploration] != 0.70 {
		t.Errorf("Expected Exploration weight=0.70, got %.2f", planner.weights[Exploration])
	}

	if planner.weights[Optimization] != 0.85 {
		t.Errorf("Expected Optimization weight=0.85, got %.2f", planner.weights[Optimization])
	}

	if planner.weights[Stabilization] != 1.00 {
		t.Errorf("Expected Stabilization weight=1.00, got %.2f", planner.weights[Stabilization])
	}
}

// TestClassifyTest validates automatic test classification
func TestClassifyTest(t *testing.T) {
	planner := NewThreeRegimePlanner()

	tests := []struct {
		name         string
		testName     string
		tags         []string
		expectedRegime TestRegime
	}{
		{
			"Happy path critical",
			"TestPaymentFlowHappyPath",
			[]string{"happy-path", "critical"},
			Stabilization,
		},
		{
			"Experimental edge case",
			"TestEdgeCaseRareScenario",
			[]string{"experimental", "edge"},
			Exploration,
		},
		{
			"Performance optimization",
			"BenchmarkDatabaseQuerySpeed",
			[]string{"benchmark", "performance"},
			Optimization,
		},
		{
			"Security validation",
			"TestAuthenticationSecurity",
			[]string{"security", "auth"},
			Stabilization,
		},
		{
			"Fuzzy exploration",
			"TestRandomInputFuzzing",
			[]string{"fuzzy", "random"},
			Exploration,
		},
		{
			"No keywords (default to Stabilization)",
			"TestSomething",
			[]string{},
			Stabilization,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			classification := planner.ClassifyTest(tt.testName, tt.tags)

			if classification.Regime != tt.expectedRegime {
				t.Errorf("Expected regime %v, got %v (rationale: %s)",
					tt.expectedRegime, classification.Regime, classification.Rationale)
			}

			expectedWeight := planner.weights[tt.expectedRegime]
			if classification.Weight != expectedWeight {
				t.Errorf("Expected weight %.2f, got %.2f",
					expectedWeight, classification.Weight)
			}

			if classification.TestName != tt.testName {
				t.Errorf("Expected testName=%s, got %s", tt.testName, classification.TestName)
			}
		})
	}
}

// TestAllocateTestEffort validates test distribution
func TestAllocateTestEffort(t *testing.T) {
	planner := NewThreeRegimePlanner()

	tests := []struct {
		name       string
		totalTests int
		expected   map[TestRegime]int
	}{
		{
			"100 tests",
			100,
			map[TestRegime]int{
				Exploration:   34,  // 33.85% ≈ 34
				Optimization:  29,  // 28.72% ≈ 29
				Stabilization: 37,  // 37.44% ≈ 37
			},
		},
		{
			"10 tests",
			10,
			map[TestRegime]int{
				Exploration:   3,  // 33.85% ≈ 3
				Optimization:  3,  // 28.72% ≈ 3
				Stabilization: 4,  // 37.44% ≈ 4 (+ rounding)
			},
		},
		{
			"1 test",
			1,
			map[TestRegime]int{
				Exploration:   0,
				Optimization:  0,
				Stabilization: 1, // All remainder goes to Stabilization
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			allocation := planner.AllocateTestEffort(tt.totalTests)

			// Check each regime
			for regime, expected := range tt.expected {
				actual := allocation[regime]
				if actual != expected {
					t.Errorf("Regime %v: expected %d tests, got %d",
						regime, expected, actual)
				}
			}

			// Ensure total matches (accounting for rounding)
			total := 0
			for _, count := range allocation {
				total += count
			}

			if total != tt.totalTests {
				t.Errorf("Expected total %d, got %d", tt.totalTests, total)
			}
		})
	}
}

// TestCalculateOverallConfidence validates weighted confidence
func TestCalculateOverallConfidence(t *testing.T) {
	planner := NewThreeRegimePlanner()

	tests := []struct {
		name     string
		results  []TestResult
		minConf  float64 // Minimum expected confidence
		maxConf  float64 // Maximum expected confidence
	}{
		{
			"All tests passing",
			[]TestResult{
				{Name: "TestCritical", Tags: []string{"critical"}, PassRate: 1.0, Passed: true},
				{Name: "TestPerformance", Tags: []string{"optimize"}, PassRate: 1.0, Passed: true},
				{Name: "TestExperimental", Tags: []string{"experimental"}, PassRate: 1.0, Passed: true},
			},
			0.95, // Should be very high
			1.00,
		},
		{
			"Exploration fails, Stabilization passes",
			[]TestResult{
				{Name: "TestCritical", Tags: []string{"critical"}, PassRate: 1.0, Passed: true},
				{Name: "TestExperimental", Tags: []string{"experimental"}, PassRate: 0.0, Passed: false},
			},
			0.70, // Exploration failure has low weight
			0.85,
		},
		{
			"Stabilization fails (critical)",
			[]TestResult{
				{Name: "TestCritical", Tags: []string{"critical"}, PassRate: 0.0, Passed: false},
				{Name: "TestExperimental", Tags: []string{"experimental"}, PassRate: 1.0, Passed: true},
			},
			0.20, // Stabilization failure heavily penalized (1.00 weight)
			0.40,
		},
		{
			"No tests",
			[]TestResult{},
			0.0,
			0.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			confidence := planner.CalculateOverallConfidence(tt.results)

			if confidence < tt.minConf || confidence > tt.maxConf {
				t.Errorf("Expected confidence in [%.2f, %.2f], got %.2f",
					tt.minConf, tt.maxConf, confidence)
			}
		})
	}
}

// TestGetRegimeForQuality validates quality-to-regime mapping
func TestGetRegimeForQuality(t *testing.T) {
	planner := NewThreeRegimePlanner()

	tests := []struct {
		quality  float64
		expected TestRegime
	}{
		{0.50, Exploration},
		{0.69, Exploration},
		{0.70, Optimization},
		{0.80, Optimization},
		{0.84, Optimization},
		{0.85, Stabilization},
		{0.95, Stabilization},
		{1.00, Stabilization},
	}

	for _, tt := range tests {
		regime := planner.GetRegimeForQuality(tt.quality)

		if regime != tt.expected {
			t.Errorf("Quality %.2f: expected %v, got %v",
				tt.quality, tt.expected, regime)
		}
	}
}

// TestValidateDistribution validates distribution sum
func TestValidateDistribution(t *testing.T) {
	planner := NewThreeRegimePlanner()

	if !planner.ValidateDistribution() {
		t.Error("Distribution validation failed - should sum to ~1.0")
	}

	// Calculate actual sum
	sum := 0.0
	for _, proportion := range planner.distribution {
		sum += proportion
	}

	if sum < 0.99 || sum > 1.01 {
		t.Errorf("Distribution sums to %.4f (expected ~1.0)", sum)
	}
}

// TestFormatAllocation validates human-readable allocation
func TestFormatAllocation(t *testing.T) {
	planner := NewThreeRegimePlanner()

	output := planner.FormatAllocation(100)

	// Should contain key information
	expected := []string{
		"100 tests",
		"Exploration",
		"Optimization",
		"Stabilization",
		"33.85%",
		"28.72%",
		"37.44%",
	}

	for _, exp := range expected {
		if !contains(output, exp) {
			t.Errorf("Output missing expected string: %s\nOutput: %s", exp, output)
		}
	}
}

// TestCalculateRegimeMetrics validates detailed regime breakdown
func TestCalculateRegimeMetrics(t *testing.T) {
	planner := NewThreeRegimePlanner()

	results := []TestResult{
		{Name: "TestCritical1", Tags: []string{"critical"}, Passed: true, PassRate: 1.0},
		{Name: "TestCritical2", Tags: []string{"critical"}, Passed: true, PassRate: 1.0},
		{Name: "TestCritical3", Tags: []string{"critical"}, Passed: false, PassRate: 0.0},
		{Name: "TestExperimental1", Tags: []string{"experimental"}, Passed: false, PassRate: 0.0},
		{Name: "TestOptimize1", Tags: []string{"performance"}, Passed: true, PassRate: 1.0},
	}

	metrics := planner.CalculateRegimeMetrics(results)

	if len(metrics) != 3 {
		t.Errorf("Expected 3 regime metrics, got %d", len(metrics))
	}

	// Find Stabilization metrics
	var stabilization *RegimeMetrics
	for i := range metrics {
		if metrics[i].Regime == Stabilization {
			stabilization = &metrics[i]
			break
		}
	}

	if stabilization == nil {
		t.Fatal("Stabilization metrics not found")
	}

	// Should have 3 critical tests
	if stabilization.TotalTests != 3 {
		t.Errorf("Expected 3 Stabilization tests, got %d", stabilization.TotalTests)
	}

	// 2 passed, 1 failed
	if stabilization.PassedTests != 2 {
		t.Errorf("Expected 2 passed, got %d", stabilization.PassedTests)
	}

	if stabilization.FailedTests != 1 {
		t.Errorf("Expected 1 failed, got %d", stabilization.FailedTests)
	}

	// Pass rate should be 2/3 ≈ 0.667
	expectedPassRate := 2.0 / 3.0
	if math.Abs(stabilization.PassRate-expectedPassRate) > 0.01 {
		t.Errorf("Expected pass rate %.3f, got %.3f",
			expectedPassRate, stabilization.PassRate)
	}

	// Weight should be 1.00
	if stabilization.Weight != 1.00 {
		t.Errorf("Expected weight 1.00, got %.2f", stabilization.Weight)
	}
}

// TestTestRegimeString validates string representation
func TestTestRegimeString(t *testing.T) {
	tests := []struct {
		regime   TestRegime
		expected string
	}{
		{Exploration, "Exploration"},
		{Optimization, "Optimization"},
		{Stabilization, "Stabilization"},
		{TestRegime(999), "Unknown"},
	}

	for _, tt := range tests {
		str := tt.regime.String()
		if str != tt.expected {
			t.Errorf("Expected %s, got %s", tt.expected, str)
		}
	}
}

// TestKeywordCounting validates keyword matching
func TestKeywordCounting(t *testing.T) {
	tests := []struct {
		text     string
		keywords []string
		expected int
	}{
		{"test critical happy-path", []string{"critical", "happy-path"}, 2},
		{"experimental edge case", []string{"experimental", "optimize"}, 1},
		{"no match", []string{"critical", "experimental"}, 0},
		{"multiple experimental experimental", []string{"experimental"}, 1}, // Only counts once
	}

	for _, tt := range tests {
		count := countKeywords(tt.text, tt.keywords)
		if count != tt.expected {
			t.Errorf("Text '%s' with keywords %v: expected %d, got %d",
				tt.text, tt.keywords, tt.expected, count)
		}
	}
}

// TestGetDistribution validates distribution retrieval
func TestGetDistribution(t *testing.T) {
	planner := NewThreeRegimePlanner()
	dist := planner.GetDistribution()

	if len(dist) != 3 {
		t.Errorf("Expected 3 regimes, got %d", len(dist))
	}

	if dist[Exploration] != 0.3385 {
		t.Errorf("Expected Exploration=0.3385, got %.4f", dist[Exploration])
	}
}

// TestGetWeights validates weights retrieval
func TestGetWeights(t *testing.T) {
	planner := NewThreeRegimePlanner()
	weights := planner.GetWeights()

	if len(weights) != 3 {
		t.Errorf("Expected 3 weights, got %d", len(weights))
	}

	if weights[Stabilization] != 1.00 {
		t.Errorf("Expected Stabilization weight=1.00, got %.2f", weights[Stabilization])
	}
}

// BenchmarkClassifyTest benchmarks test classification
func BenchmarkClassifyTest(b *testing.B) {
	planner := NewThreeRegimePlanner()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = planner.ClassifyTest("TestPaymentFlowHappyPath", []string{"happy-path", "critical"})
	}
}

// BenchmarkCalculateOverallConfidence benchmarks confidence calculation
func BenchmarkCalculateOverallConfidence(b *testing.B) {
	planner := NewThreeRegimePlanner()

	results := []TestResult{
		{Name: "TestCritical", Tags: []string{"critical"}, Passed: true, PassRate: 1.0},
		{Name: "TestExperimental", Tags: []string{"experimental"}, Passed: true, PassRate: 1.0},
		{Name: "TestPerformance", Tags: []string{"performance"}, Passed: true, PassRate: 1.0},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = planner.CalculateOverallConfidence(results)
	}
}

// Helper function
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && stringContains(s, substr))
}

func stringContains(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
