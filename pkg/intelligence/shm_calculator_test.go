package intelligence

import (
	"context"
	"testing"

	"github.com/asymmetrica/urbanlens/pkg/intelligence/sonars"
)

// TestSHMCalculation validates System Health Metric computation
func TestSHMCalculation(t *testing.T) {
	shm := NewSHMCalculator()

	// Test weighted average formula
	scores := map[string]float64{
		"ux":       0.90,
		"design":   0.85,
		"code":     0.75,
		"semantic": 0.80,
		"journey":  0.95,
		"state":    0.70,
	}

	result := shm.computeWeightedSHM(scores)

	// Expected: (0.90×0.25 + 0.85×0.25 + 0.75×0.125 + 0.80×0.125 + 0.95×0.125 + 0.70×0.125)
	// = (0.225 + 0.2125 + 0.09375 + 0.10 + 0.11875 + 0.0875) = 0.8375
	expected := 0.8375

	if result < expected-0.01 || result > expected+0.01 {
		t.Errorf("SHM calculation incorrect: got %.4f, expected %.4f", result, expected)
	}
}

// TestRegimeDetermination validates regime classification
func TestRegimeDetermination(t *testing.T) {
	shm := NewSHMCalculator()

	tests := []struct {
		shmValue float64
		expected Regime
	}{
		{0.50, RegimeExploration},
		{0.69, RegimeExploration},
		{0.70, RegimeOptimization},
		{0.84, RegimeOptimization},
		{0.85, RegimeStabilization},
		{0.95, RegimeStabilization},
	}

	for _, test := range tests {
		result := shm.determineRegime(test.shmValue)
		if result != test.expected {
			t.Errorf("Regime determination failed for SHM %.2f: got %s, expected %s",
				test.shmValue, result, test.expected)
		}
	}
}

// TestWilliamsDriftDetection validates drift detection algorithm
func TestWilliamsDriftDetection(t *testing.T) {
	shm := NewSHMCalculator()

	// Test case: 100 commits since baseline, SHM changed from 0.85 to 0.87
	baselineSHM := 0.85
	currentSHM := 0.87
	commits := 100

	approved, driftPercent := shm.WilliamsDriftDetection(currentSHM, baselineSHM, commits)

	// Williams threshold for t=100: √100 × log₂(100) × 0.05 = 10 × 6.64 × 0.05 = 3.32%
	// Drift: (0.87 - 0.85) / 0.85 × 100 = 2.35%
	// Should be approved (2.35% < 3.32%)

	if !approved {
		t.Errorf("Drift detection failed: drift %.2f%% should be approved", driftPercent)
	}

	// Test case: Large drift should be rejected
	currentSHM = 0.95
	approved, driftPercent = shm.WilliamsDriftDetection(currentSHM, baselineSHM, commits)

	// Drift: (0.95 - 0.85) / 0.85 × 100 = 11.76%
	// Should be rejected (11.76% > 3.32%)

	if approved {
		t.Errorf("Drift detection failed: drift %.2f%% should be rejected", driftPercent)
	}
}

// TestFindExtremes validates weakest/strongest dimension detection
func TestFindExtremes(t *testing.T) {
	shm := NewSHMCalculator()

	scores := map[string]float64{
		"ux":       0.90,
		"design":   0.85,
		"code":     0.60, // Weakest
		"semantic": 0.80,
		"journey":  0.95, // Strongest
		"state":    0.70,
	}

	weakest, strongest := shm.findExtremes(scores)

	if weakest != "code" {
		t.Errorf("Weakest dimension detection failed: got %s, expected code", weakest)
	}

	if strongest != "journey" {
		t.Errorf("Strongest dimension detection failed: got %s, expected journey", strongest)
	}
}

// TestFullSHMCalculation runs complete SHM analysis
func TestFullSHMCalculation(t *testing.T) {
	shm := NewSHMCalculator()

	// Create test app
	app := &sonars.AppState{
		RootPath: "/tmp/test-app",
		AppType:  "TodoApp",
		Backend: &sonars.BackendInfo{
			Language:     "go",
			EntryPoint:   "main.go",
			APIEndpoints: 5,
			Handlers:     []string{"handlers/todo.go", "handlers/user.go"},
		},
		Frontend: &sonars.FrontendInfo{
			Framework:  "react",
			EntryPoint: "App.tsx",
			Components: []string{"Todo.tsx", "TodoList.tsx", "TodoItem.tsx"},
			Routes:     []string{"/", "/todos", "/about"},
		},
		Database: &sonars.DatabaseInfo{
			Type:       "postgres",
			SchemaFile: "schema.sql",
			Tables:     []string{"todos", "users"},
		},
	}

	ctx := context.Background()
	result, err := shm.CalculateSHM(ctx, app)

	if err != nil {
		t.Fatalf("SHM calculation failed: %v", err)
	}

	// Validate result structure
	if result.SHM < 0.0 || result.SHM > 1.0 {
		t.Errorf("SHM out of range: %.3f", result.SHM)
	}

	if result.Regime == "" {
		t.Error("Regime not determined")
	}

	if len(result.SonarScores) != 6 {
		t.Errorf("Expected 6 sonar scores, got %d", len(result.SonarScores))
	}

	if len(result.SonarReports) != 6 {
		t.Errorf("Expected 6 sonar reports, got %d", len(result.SonarReports))
	}

	if result.WeakestDimension == "" {
		t.Error("Weakest dimension not identified")
	}

	if result.StrongestDimension == "" {
		t.Error("Strongest dimension not identified")
	}

	// Validate all sonar scores are in valid range
	for sonar, score := range result.SonarScores {
		if score < 0.0 || score > 1.0 {
			t.Errorf("Sonar %s score out of range: %.3f", sonar, score)
		}
	}

	// Validate all reports have content
	for sonar, report := range result.SonarReports {
		if report == nil {
			t.Errorf("Sonar %s report is nil", sonar)
			continue
		}

		if report.Summary == "" {
			t.Errorf("Sonar %s report has empty summary", sonar)
		}

		if report.Status == "" {
			t.Errorf("Sonar %s report has no status", sonar)
		}
	}
}

// TestDashboardGeneration validates dashboard visualization
func TestDashboardGeneration(t *testing.T) {
	shm := NewSHMCalculator()

	result := &SHMResult{
		SHM:    0.82,
		Regime: RegimeOptimization,
		SonarScores: map[string]float64{
			"ux":       0.90,
			"design":   0.85,
			"code":     0.70,
			"semantic": 0.80,
			"journey":  0.95,
			"state":    0.75,
		},
		SonarReports: map[string]*sonars.Report{
			"ux":       {Summary: "UX Summary", Status: sonars.StatusExcellent, Recommendations: []string{"Rec 1", "Rec 2"}},
			"design":   {Summary: "Design Summary", Status: sonars.StatusExcellent, Recommendations: []string{}},
			"code":     {Summary: "Code Summary", Status: sonars.StatusOK, Recommendations: []string{"Improve complexity"}},
			"semantic": {Summary: "Semantic Summary", Status: sonars.StatusOK, Recommendations: []string{}},
			"journey":  {Summary: "Journey Summary", Status: sonars.StatusExcellent, Recommendations: []string{}},
			"state":    {Summary: "State Summary", Status: sonars.StatusOK, Recommendations: []string{}},
		},
		WeakestDimension:   "code",
		StrongestDimension: "journey",
	}

	dashboard := shm.GenerateDashboard(result)

	// Validate dashboard contains key sections
	if dashboard == "" {
		t.Fatal("Dashboard is empty")
	}

	// Check for expected content
	expectedSections := []string{
		"UNIFIED INTELLIGENCE MONITORING SYSTEM",
		"System Health Metric (SHM)",
		"SIX SONAR ENGINES",
		"Strongest Dimension",
		"Weakest Dimension",
		"Top Recommendations",
	}

	for _, section := range expectedSections {
		if !containsString(dashboard, section) {
			t.Errorf("Dashboard missing section: %s", section)
		}
	}
}

// BenchmarkSHMCalculation measures SHM calculation performance
func BenchmarkSHMCalculation(b *testing.B) {
	shm := NewSHMCalculator()

	app := &sonars.AppState{
		RootPath: "/tmp/benchmark-app",
		AppType:  "TodoApp",
		Backend: &sonars.BackendInfo{
			Language:     "go",
			APIEndpoints: 10,
			Handlers:     []string{"handlers/todo.go"},
		},
		Frontend: &sonars.FrontendInfo{
			Framework:  "react",
			Components: []string{"Todo.tsx"},
			Routes:     []string{"/"},
		},
	}

	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := shm.CalculateSHM(ctx, app)
		if err != nil {
			b.Fatalf("SHM calculation failed: %v", err)
		}
	}
}

// containsString checks if string s contains substring substr
func containsString(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && containsStringRecursive(s, substr, 0))
}

func containsStringRecursive(s, substr string, i int) bool {
	if i+len(substr) > len(s) {
		return false
	}
	if s[i:i+len(substr)] == substr {
		return true
	}
	return containsStringRecursive(s, substr, i+1)
}
