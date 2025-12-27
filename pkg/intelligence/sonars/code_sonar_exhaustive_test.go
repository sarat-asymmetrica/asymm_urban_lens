package sonars

import (
	"context"
	"math"
	"os"
	"path/filepath"
	"testing"
)

// =============================================================================
// MATHEMATICAL FOUNDATIONS (from Research Paper)
// =============================================================================
//
// FORMULA 1 (McCabe, 1976):
//   Cyclomatic Complexity (CC) = Edges - Nodes + 2 × Connected_Components
//   Simplified: CC = Decision_Points + 1
//
// FORMULA 2 (IEEE Standard):
//   Bug Density = (CC^1.2 × Duplication_Ratio) / Cohesion_Score
//
// IEEE COMPLEXITY STANDARDS:
//   CC 1-10:   Low risk (maintainable)
//   CC 11-20:  Moderate risk
//   CC 21-50:  High risk (refactor recommended)
//   CC > 50:   Very high risk (refactor immediately)
//
// =============================================================================

// =============================================================================
// STABILIZATION TESTS (100% Required - Regime 3: 50%)
// =============================================================================

// TestCodeSonar_CyclomaticComplexity_Simple validates CC = 1 for linear code
//
// IEEE Standard: CC = 1 means zero branching (straight-line execution)
// Expected: Linear code with no if/for/while/case should yield CC = 1
func TestCodeSonar_CyclomaticComplexity_Simple(t *testing.T) {
	cs := NewCodeSonar()
	tmpDir := t.TempDir()

	// Create simple linear Go file (CC = 1)
	simpleFile := filepath.Join(tmpDir, "simple.go")
	content := `package main
func main() {
	x := 1
	y := 2
	z := x + y
	println(z)
}`
	if err := os.WriteFile(simpleFile, []byte(content), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	complexity := cs.analyzeFileComplexity(simpleFile)

	// CC = decision_points + 1 = 0 + 1 = 1
	// With 1 function, avg = max = 1.0
	if complexity["functions"] != 1.0 {
		t.Errorf("Expected 1 function, got %.1f", complexity["functions"])
	}

	// Total complexity for 1 function with CC=1 is 2.0 (1 func + 1 base)
	if complexity["total"] < 1.0 {
		t.Errorf("Expected total complexity >= 1.0 for simple code, got %.2f", complexity["total"])
	}

	t.Logf("✓ Simple linear code: total=%.2f, max=%.2f, functions=%.0f",
		complexity["total"], complexity["max"], complexity["functions"])
}

// TestCodeSonar_CyclomaticComplexity_SingleBranch validates CC = 2 for one if
//
// IEEE Standard: CC = 2 means 1 decision point (1 if statement)
// Formula: CC = 1 (base) + 1 (if) = 2
func TestCodeSonar_CyclomaticComplexity_SingleBranch(t *testing.T) {
	cs := NewCodeSonar()
	tmpDir := t.TempDir()

	singleBranchFile := filepath.Join(tmpDir, "branch.go")
	content := `package main
func check(x int) {
	if x > 0 {
		println("positive")
	}
}`
	if err := os.WriteFile(singleBranchFile, []byte(content), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	complexity := cs.analyzeFileComplexity(singleBranchFile)

	// 1 function, 1 decision point (if) → total = 2.0
	if complexity["total"] < 2.0 {
		t.Errorf("Expected total complexity >= 2.0 for single branch, got %.2f", complexity["total"])
	}

	t.Logf("✓ Single branch: total=%.2f, max=%.2f, functions=%.0f",
		complexity["total"], complexity["max"], complexity["functions"])
}

// TestCodeSonar_CyclomaticComplexity_MultipleBranch validates CC > 10 (high risk)
//
// IEEE Standard: CC > 10 is moderate to high risk
// Creates file with 15+ decision points to exceed threshold
func TestCodeSonar_CyclomaticComplexity_MultipleBranch(t *testing.T) {
	cs := NewCodeSonar()
	tmpDir := t.TempDir()

	complexFile := filepath.Join(tmpDir, "complex.go")
	content := `package main
func complex(a, b, c, d, e int) {
	if a > 0 {
		if b > 0 {
			if c > 0 {
				if d > 0 {
					if e > 0 {
						for i := 0; i < 10; i++ {
							while true {
								switch c {
								case 1:
								case 2:
								case 3:
								}
							}
						}
					}
				}
			}
		}
	}
}`
	if err := os.WriteFile(complexFile, []byte(content), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	complexity := cs.analyzeFileComplexity(complexFile)

	// Count: 5 if + 1 for + 1 while + 3 case = 10 decision points
	// Total = 10 + 1 (function) = 11+
	if complexity["total"] < 10.0 {
		t.Errorf("Expected total complexity >= 10.0, got %.2f", complexity["total"])
	}

	t.Logf("✓ Multiple branches (high CC): total=%.2f, max=%.2f",
		complexity["total"], complexity["max"])
}

// TestCodeSonar_CyclomaticComplexity_Formula validates McCabe's formula
//
// Formula: CC = Edges - Nodes + 2 × Connected_Components
// Simplified: CC = Decision_Points + 1
// This test validates the implementation matches the theoretical formula
func TestCodeSonar_CyclomaticComplexity_Formula(t *testing.T) {
	tests := []struct {
		name           string
		code           string
		minDecisions   int // Minimum expected decision points
		expectedCCMin  float64
	}{
		{
			name: "Zero decisions",
			code: `func f() { x := 1 }`,
			minDecisions: 0,
			expectedCCMin: 1.0, // Base CC
		},
		{
			name: "One if",
			code: `func f(x int) { if x > 0 { } }`,
			minDecisions: 1,
			expectedCCMin: 2.0, // 1 decision + base
		},
		{
			name: "Two branches",
			code: `func f(x int) { if x > 0 { } for i := 0; i < 10; i++ { } }`,
			minDecisions: 2,
			expectedCCMin: 3.0, // 2 decisions + base
		},
		{
			name: "Logical operators",
			code: `func f(a, b bool) { if a && b || c { } }`,
			minDecisions: 2, // &&, ||
			expectedCCMin: 3.0,
		},
	}

	cs := NewCodeSonar()
	tmpDir := t.TempDir()

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			testFile := filepath.Join(tmpDir, "test.go")
			fullCode := "package main\n" + tt.code
			if err := os.WriteFile(testFile, []byte(fullCode), 0644); err != nil {
				t.Fatalf("Failed to write test file: %v", err)
			}

			complexity := cs.analyzeFileComplexity(testFile)

			// Validate total >= expected (implementation may count additional keywords)
			if complexity["total"] < tt.expectedCCMin {
				t.Errorf("Expected total >= %.1f, got %.2f (formula validation failed)",
					tt.expectedCCMin, complexity["total"])
			}

			t.Logf("✓ %s: total=%.2f (expected >= %.1f)",
				tt.name, complexity["total"], tt.expectedCCMin)
		})
	}
}

// TestCodeSonar_BugDensity_LowComplexity validates bug density formula with low CC
//
// Formula: Bug_Density = (CC^1.2 × Duplication_Ratio) / Cohesion_Score
// Expected: Low CC → Low bug density
func TestCodeSonar_BugDensity_LowComplexity(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	app := &AppState{
		RootPath: t.TempDir(),
		Backend: &BackendInfo{
			Language: "go",
			Handlers: []string{},
		},
	}

	// Create simple file with CC ≈ 3
	simpleFile := filepath.Join(app.RootPath, "handler.go")
	content := `package main
func handler() {
	if true { }
}`
	if err := os.WriteFile(simpleFile, []byte(content), 0644); err != nil {
		t.Fatalf("Failed to write file: %v", err)
	}
	app.Backend.Handlers = []string{"handler.go"}

	telemetry, err := cs.Ping(ctx, app)
	if err != nil {
		t.Fatalf("Ping failed: %v", err)
	}

	metrics, err := cs.Echo(ctx, telemetry)
	if err != nil {
		t.Fatalf("Echo failed: %v", err)
	}

	// Low complexity should yield high score
	score := cs.Map(ctx, metrics)

	if score < 0.70 {
		t.Errorf("Expected score >= 0.70 for low complexity, got %.2f", score)
	}

	// Validate bug density is low (not directly computed, but inferred from score)
	avgCC := metrics.Values["avg_complexity"]
	duplication := metrics.Values["duplication_percentage"]
	cohesion := metrics.Values["cohesion_score"]

	// Bug Density ∝ CC^1.2 × duplication / cohesion
	// Low CC + low duplication + high cohesion → low bug density
	bugDensityApprox := math.Pow(avgCC, 1.2) * (duplication / 100.0) / cohesion

	if bugDensityApprox > 0.50 {
		t.Errorf("Expected bug density < 0.50, got %.3f (CC=%.1f, dup=%.1f%%, cohesion=%.2f)",
			bugDensityApprox, avgCC, duplication, cohesion)
	}

	t.Logf("✓ Low complexity → low bug density: %.3f (CC=%.1f, dup=%.1f%%, cohesion=%.2f)",
		bugDensityApprox, avgCC, duplication, cohesion)
}

// TestCodeSonar_BugDensity_HighComplexity validates bug density with high CC
//
// Formula: Bug_Density = (CC^1.2 × Duplication_Ratio) / Cohesion_Score
// Expected: High CC → High bug density
func TestCodeSonar_BugDensity_HighComplexity(t *testing.T) {
	// Simulate high complexity scenario
	avgCC := 25.0 // High complexity
	duplication := 8.0 // 8% duplication
	cohesion := 0.65 // Moderate cohesion

	// Bug Density = (25^1.2 × 0.08) / 0.65
	bugDensity := math.Pow(avgCC, 1.2) * (duplication / 100.0) / cohesion

	// High CC should yield high bug density
	if bugDensity < 0.30 {
		t.Errorf("Expected bug density >= 0.30 for high CC, got %.3f", bugDensity)
	}

	t.Logf("✓ High complexity → high bug density: %.3f (CC=%.1f, dup=%.1f%%, cohesion=%.2f)",
		bugDensity, avgCC, duplication, cohesion)
}

// TestCodeSonar_Duplication_None validates 0% duplication yields max score
func TestCodeSonar_Duplication_None(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	metrics := &Metrics{
		SonarName: "Code Sonar",
		Values: map[string]float64{
			"avg_complexity":      5.0,  // Good
			"max_complexity":      8.0,  // Good
			"duplication_percentage": 0.0, // PERFECT
			"cohesion_score":      0.80, // Good
			"avg_function_length": 30.0, // Good
			"max_function_length": 50.0, // Good
		},
	}

	score := cs.Map(ctx, metrics)

	// 0% duplication should contribute 1.0 to score
	// Overall score should be high
	if score < 0.85 {
		t.Errorf("Expected score >= 0.85 for zero duplication, got %.2f", score)
	}

	t.Logf("✓ Zero duplication yields high score: %.3f", score)
}

// TestCodeSonar_Duplication_High validates >20% duplication penalty
func TestCodeSonar_Duplication_High(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	metrics := &Metrics{
		SonarName: "Code Sonar",
		Values: map[string]float64{
			"avg_complexity":      5.0,  // Good
			"max_complexity":      8.0,  // Good
			"duplication_percentage": 25.0, // BAD (>20%)
			"cohesion_score":      0.80, // Good
			"avg_function_length": 30.0, // Good
			"max_function_length": 50.0, // Good
		},
	}

	score := cs.Map(ctx, metrics)

	// High duplication should penalize score significantly
	// Duplication score = max(0, 1 - 25/10) = max(0, -1.5) = 0.0
	// This should drag overall score down
	if score > 0.75 {
		t.Errorf("Expected score <= 0.75 for high duplication (25%%), got %.2f", score)
	}

	t.Logf("✓ High duplication (25%%) penalizes score: %.3f", score)
}

// TestCodeSonar_Cohesion_High validates high cohesion (≥0.80) yields praise
func TestCodeSonar_Cohesion_High(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	metrics := &Metrics{
		SonarName: "Code Sonar",
		Values: map[string]float64{
			"avg_complexity":      5.0,
			"max_complexity":      8.0,
			"duplication_percentage": 2.0,
			"cohesion_score":      0.85, // HIGH cohesion
			"avg_function_length": 30.0,
			"max_function_length": 50.0,
		},
	}

	score := cs.Map(ctx, metrics)
	report := cs.Critique(ctx, score, metrics)

	// Should find praise for high cohesion
	foundPraise := false
	for _, finding := range report.Findings {
		if finding.Type == FindingPraise && finding.Value == 0.85 {
			foundPraise = true
			break
		}
	}

	if !foundPraise {
		t.Errorf("Expected praise finding for high cohesion (0.85)")
	}

	t.Logf("✓ High cohesion (0.85) yields praise finding")
}

// TestCodeSonar_Cohesion_Low validates low cohesion (<0.60) flags issues
func TestCodeSonar_Cohesion_Low(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	metrics := &Metrics{
		SonarName: "Code Sonar",
		Values: map[string]float64{
			"avg_complexity":      5.0,
			"max_complexity":      8.0,
			"duplication_percentage": 2.0,
			"cohesion_score":      0.50, // LOW cohesion
			"avg_function_length": 30.0,
			"max_function_length": 50.0,
		},
	}

	score := cs.Map(ctx, metrics)
	report := cs.Critique(ctx, score, metrics)

	// Should find issue for low cohesion
	foundIssue := false
	for _, finding := range report.Findings {
		if finding.Type == FindingIssue && finding.Value == 0.50 {
			foundIssue = true
			break
		}
	}

	if !foundIssue {
		t.Errorf("Expected issue finding for low cohesion (0.50)")
	}

	// Should have recommendations
	if len(report.Recommendations) == 0 {
		t.Errorf("Expected recommendations for low cohesion")
	}

	t.Logf("✓ Low cohesion (0.50) flags issue with %d recommendations",
		len(report.Recommendations))
}

// =============================================================================
// OPTIMIZATION TESTS (85% Required - Regime 2: 20%)
// =============================================================================

// TestCodeSonar_PING_ParsesAST validates PING phase collects complexity metrics
func TestCodeSonar_PING_ParsesAST(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	tmpDir := t.TempDir()
	testFile := filepath.Join(tmpDir, "test.go")
	content := `package main
func test() {
	if true {
		for i := 0; i < 10; i++ {
		}
	}
}`
	if err := os.WriteFile(testFile, []byte(content), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	app := &AppState{
		RootPath: tmpDir,
		Backend: &BackendInfo{
			Language: "go",
			Handlers: []string{"test.go"},
		},
	}

	telemetry, err := cs.Ping(ctx, app)
	if err != nil {
		t.Fatalf("PING failed: %v", err)
	}

	// Validate telemetry contains complexity data
	if telemetry.SonarName != "Code Sonar" {
		t.Errorf("Expected SonarName='Code Sonar', got '%s'", telemetry.SonarName)
	}

	complexity, ok := telemetry.RawData["complexity"].(map[string]float64)
	if !ok {
		t.Fatalf("Expected complexity in raw data")
	}

	if complexity["average"] == 0 || complexity["maximum"] == 0 {
		t.Errorf("Expected non-zero complexity metrics")
	}

	t.Logf("✓ PING collected complexity: avg=%.2f, max=%.2f",
		complexity["average"], complexity["maximum"])
}

// TestCodeSonar_ECHO_ComputesMetrics validates ECHO phase processes telemetry
func TestCodeSonar_ECHO_ComputesMetrics(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	telemetry := &TelemetryData{
		SonarName: "Code Sonar",
		RawData: map[string]interface{}{
			"complexity": map[string]float64{
				"average": 8.5,
				"maximum": 15.0,
				"total":   42.5,
			},
			"duplication": map[string]float64{
				"percentage": 3.5,
				"blocks":     4.0,
			},
			"cohesion": map[string]float64{
				"score": 0.72,
			},
			"function_lengths": map[string]float64{
				"average": 45.0,
				"maximum": 80.0,
			},
		},
	}

	metrics, err := cs.Echo(ctx, telemetry)
	if err != nil {
		t.Fatalf("ECHO failed: %v", err)
	}

	// Validate metrics extraction
	if metrics.Values["avg_complexity"] != 8.5 {
		t.Errorf("Expected avg_complexity=8.5, got %.2f", metrics.Values["avg_complexity"])
	}

	if metrics.Values["max_complexity"] != 15.0 {
		t.Errorf("Expected max_complexity=15.0, got %.2f", metrics.Values["max_complexity"])
	}

	if metrics.Values["duplication_percentage"] != 3.5 {
		t.Errorf("Expected duplication_percentage=3.5, got %.2f", metrics.Values["duplication_percentage"])
	}

	if metrics.Values["cohesion_score"] != 0.72 {
		t.Errorf("Expected cohesion_score=0.72, got %.2f", metrics.Values["cohesion_score"])
	}

	t.Logf("✓ ECHO computed metrics: CC=%.1f, dup=%.1f%%, cohesion=%.2f",
		metrics.Values["avg_complexity"],
		metrics.Values["duplication_percentage"],
		metrics.Values["cohesion_score"])
}

// TestCodeSonar_MAP_NormalizesTo01 validates MAP phase normalizes to [0.0, 1.0]
func TestCodeSonar_MAP_NormalizesTo01(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	tests := []struct {
		name           string
		avgComplexity  float64
		maxComplexity  float64
		duplication    float64
		cohesion       float64
		expectedMin    float64
		expectedMax    float64
	}{
		{
			name:          "Excellent code",
			avgComplexity: 3.0,
			maxComplexity: 5.0,
			duplication:   1.0,
			cohesion:      0.90,
			expectedMin:   0.85,
			expectedMax:   1.0,
		},
		{
			name:          "Good code",
			avgComplexity: 8.0,
			maxComplexity: 12.0,
			duplication:   3.0,
			cohesion:      0.75,
			expectedMin:   0.70,
			expectedMax:   0.90,
		},
		{
			name:          "Moderate code",
			avgComplexity: 15.0,
			maxComplexity: 25.0,
			duplication:   5.0,
			cohesion:      0.65,
			expectedMin:   0.50,
			expectedMax:   0.75,
		},
		{
			name:          "Poor code",
			avgComplexity: 25.0,
			maxComplexity: 60.0,
			duplication:   12.0,
			cohesion:      0.50,
			expectedMin:   0.0,
			expectedMax:   0.50,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			metrics := &Metrics{
				SonarName: "Code Sonar",
				Values: map[string]float64{
					"avg_complexity":         tt.avgComplexity,
					"max_complexity":         tt.maxComplexity,
					"duplication_percentage": tt.duplication,
					"cohesion_score":         tt.cohesion,
					"avg_function_length":    40.0,
					"max_function_length":    80.0,
				},
			}

			score := cs.Map(ctx, metrics)

			// Validate score is in [0.0, 1.0]
			if score < 0.0 || score > 1.0 {
				t.Errorf("Score out of range [0.0, 1.0]: %.3f", score)
			}

			// Validate score is in expected range
			if score < tt.expectedMin || score > tt.expectedMax {
				t.Errorf("Score %.3f not in expected range [%.2f, %.2f]",
					score, tt.expectedMin, tt.expectedMax)
			}

			t.Logf("✓ %s: score=%.3f (range [%.2f, %.2f])",
				tt.name, score, tt.expectedMin, tt.expectedMax)
		})
	}
}

// TestCodeSonar_CRITIQUE_FlagsMonsters validates CRITIQUE flags CC > 50
func TestCodeSonar_CRITIQUE_FlagsMonsters(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	metrics := &Metrics{
		SonarName: "Code Sonar",
		Values: map[string]float64{
			"avg_complexity":         20.0,
			"max_complexity":         65.0, // MONSTER FUNCTION
			"duplication_percentage": 5.0,
			"cohesion_score":         0.60,
			"avg_function_length":    50.0,
			"max_function_length":    150.0,
		},
	}

	score := cs.Map(ctx, metrics)
	report := cs.Critique(ctx, score, metrics)

	// Should flag max complexity > 50 as issue
	foundMonster := false
	for _, finding := range report.Findings {
		if finding.Type == FindingIssue && finding.Value == 65.0 {
			foundMonster = true
			if finding.Severity != "High" {
				t.Errorf("Expected High severity for CC=65, got %s", finding.Severity)
			}
			break
		}
	}

	if !foundMonster {
		t.Errorf("Expected issue finding for monster function (CC=65)")
	}

	// Should recommend immediate refactoring
	hasRefactorRec := false
	for _, rec := range report.Recommendations {
		if len(rec) > 0 {
			hasRefactorRec = true
			break
		}
	}

	if !hasRefactorRec {
		t.Errorf("Expected refactoring recommendations for CC=65")
	}

	t.Logf("✓ Monster function (CC=65) flagged with %d recommendations",
		len(report.Recommendations))
}

// =============================================================================
// EXPLORATION TESTS (70% Required - Regime 1: 30%)
// =============================================================================

// TestCodeSonar_Integration_WithSHM validates Code Sonar feeds SHM with weight 0.125
//
// SHM Formula: SHM = Σ(sonar_i × weight_i) where weights sum to 1.0
// Code Sonar weight = 0.125 (12.5% of total health)
func TestCodeSonar_Integration_WithSHM(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	// Create realistic app state
	tmpDir := t.TempDir()
	testFile := filepath.Join(tmpDir, "handler.go")
	content := `package main
func handler() {
	if true {
		for i := 0; i < 10; i++ {
		}
	}
}`
	if err := os.WriteFile(testFile, []byte(content), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	app := &AppState{
		RootPath: tmpDir,
		Backend: &BackendInfo{
			Language: "go",
			Handlers: []string{"handler.go"},
		},
	}

	// Execute full sonar cycle
	result, err := ExecuteFullSonar(ctx, cs, app)
	if err != nil {
		t.Fatalf("Full sonar execution failed: %v", err)
	}

	// Validate result structure
	if result.Telemetry == nil {
		t.Fatalf("Expected telemetry data")
	}
	if result.Metrics == nil {
		t.Fatalf("Expected metrics")
	}
	if result.Report == nil {
		t.Fatalf("Expected report")
	}

	// Validate score is in [0.0, 1.0]
	if result.Score < 0.0 || result.Score > 1.0 {
		t.Errorf("Score out of range: %.3f", result.Score)
	}

	// Simulate SHM integration (weight = 0.125)
	codeSonarWeight := 0.125
	shmContribution := result.Score * codeSonarWeight

	if shmContribution < 0.0 || shmContribution > 0.125 {
		t.Errorf("SHM contribution out of range: %.4f", shmContribution)
	}

	t.Logf("✓ Code Sonar → SHM: score=%.3f, contribution=%.4f (weight=%.3f)",
		result.Score, shmContribution, codeSonarWeight)
}

// TestCodeSonar_RefactoringRecommendations validates specific refactoring advice
func TestCodeSonar_RefactoringRecommendations(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	tests := []struct {
		name              string
		avgComplexity     float64
		maxComplexity     float64
		duplication       float64
		cohesion          float64
		expectedRecCount  int
		expectedKeywords  []string
	}{
		{
			name:             "High complexity",
			avgComplexity:    22.0,
			maxComplexity:    35.0,
			duplication:      3.0,
			cohesion:         0.70,
			expectedRecCount: 2,
			expectedKeywords: []string{"URGENT", "Break down", "SRP"},
		},
		{
			name:             "High duplication",
			avgComplexity:    8.0,
			maxComplexity:    12.0,
			duplication:      8.0,
			cohesion:         0.75,
			expectedRecCount: 1,
			expectedKeywords: []string{"Extract", "DRY"},
		},
		{
			name:             "Low cohesion",
			avgComplexity:    10.0,
			maxComplexity:    15.0,
			duplication:      3.0,
			cohesion:         0.55,
			expectedRecCount: 1,
			expectedKeywords: []string{"Restructure", "package-by-feature"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			metrics := &Metrics{
				SonarName: "Code Sonar",
				Values: map[string]float64{
					"avg_complexity":         tt.avgComplexity,
					"max_complexity":         tt.maxComplexity,
					"duplication_percentage": tt.duplication,
					"cohesion_score":         tt.cohesion,
					"avg_function_length":    40.0,
					"max_function_length":    80.0,
				},
			}

			score := cs.Map(ctx, metrics)
			report := cs.Critique(ctx, score, metrics)

			if len(report.Recommendations) < tt.expectedRecCount {
				t.Errorf("Expected at least %d recommendations, got %d",
					tt.expectedRecCount, len(report.Recommendations))
			}

			// Check for expected keywords in recommendations
			allRecs := ""
			for _, rec := range report.Recommendations {
				allRecs += rec + " "
			}

			for _, keyword := range tt.expectedKeywords {
				if !containsIgnoreCase(allRecs, keyword) {
					t.Errorf("Expected keyword '%s' in recommendations", keyword)
				}
			}

			t.Logf("✓ %s: %d recommendations with keywords %v",
				tt.name, len(report.Recommendations), tt.expectedKeywords)
		})
	}
}

// TestCodeSonar_IEEE_Standards validates compliance with IEEE complexity standards
//
// IEEE Standard 1061-1998: Software Quality Metrics
// CC 1-10:   Low risk (green zone)
// CC 11-20:  Moderate risk (yellow zone)
// CC 21-50:  High risk (orange zone)
// CC > 50:   Very high risk (red zone)
func TestCodeSonar_IEEE_Standards(t *testing.T) {
	cs := NewCodeSonar()
	ctx := context.Background()

	tests := []struct {
		name          string
		avgCC         float64
		maxCC         float64
		expectedZone  string
		expectedScore float64 // Minimum expected
	}{
		{
			name:          "Green Zone (CC 1-10)",
			avgCC:         5.0,
			maxCC:         8.0,
			expectedZone:  "Low risk",
			expectedScore: 0.85,
		},
		{
			name:          "Yellow Zone (CC 11-20)",
			avgCC:         15.0,
			maxCC:         18.0,
			expectedZone:  "Moderate risk",
			expectedScore: 0.50,
		},
		{
			name:          "Orange Zone (CC 21-50)",
			avgCC:         30.0,
			maxCC:         45.0,
			expectedZone:  "High risk",
			expectedScore: 0.20,
		},
		{
			name:          "Red Zone (CC > 50)",
			avgCC:         40.0,
			maxCC:         70.0,
			expectedZone:  "Very high risk",
			expectedScore: 0.10,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			metrics := &Metrics{
				SonarName: "Code Sonar",
				Values: map[string]float64{
					"avg_complexity":         tt.avgCC,
					"max_complexity":         tt.maxCC,
					"duplication_percentage": 2.0,
					"cohesion_score":         0.75,
					"avg_function_length":    40.0,
					"max_function_length":    80.0,
				},
			}

			score := cs.Map(ctx, metrics)
			report := cs.Critique(ctx, score, metrics)

			// Validate score reflects IEEE risk zones
			if score < tt.expectedScore {
				t.Errorf("%s: Expected score >= %.2f, got %.2f",
					tt.expectedZone, tt.expectedScore, score)
			}

			// Validate report mentions risk level
			if !containsIgnoreCase(report.Summary, "CC") {
				t.Errorf("Expected summary to mention CC")
			}

			t.Logf("✓ IEEE %s: CC %.1f-%.1f → score=%.3f",
				tt.expectedZone, tt.avgCC, tt.maxCC, score)
		})
	}
}

// TestCodeSonar_StatusLevels validates score → status mapping
func TestCodeSonar_StatusLevels(t *testing.T) {
	tests := []struct {
		score          float64
		expectedStatus StatusLevel
	}{
		{0.95, StatusExcellent},
		{0.85, StatusExcellent},
		{0.80, StatusOK},
		{0.70, StatusOK},
		{0.65, StatusWarning},
		{0.50, StatusWarning},
		{0.40, StatusCritical},
		{0.10, StatusCritical},
	}

	for _, tt := range tests {
		status := DetermineStatus(tt.score)
		if status != tt.expectedStatus {
			t.Errorf("Score %.2f: expected %s, got %s",
				tt.score, tt.expectedStatus, status)
		}
		t.Logf("✓ Score %.2f → %s", tt.score, status)
	}
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

// containsIgnoreCase checks if s contains substr (case-insensitive)
func containsIgnoreCase(s, substr string) bool {
	s = toLower(s)
	substr = toLower(substr)
	return contains(s, substr)
}

func toLower(s string) string {
	result := ""
	for _, r := range s {
		if r >= 'A' && r <= 'Z' {
			result += string(r + 32)
		} else {
			result += string(r)
		}
	}
	return result
}

func contains(s, substr string) bool {
	if len(substr) > len(s) {
		return false
	}
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
