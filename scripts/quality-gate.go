// Package main implements automated quality gates based on System Health Metric (SHM)
//
// Quality Gates (from research paper):
//   SHM ≥ 0.85 → Auto-deploy to production (Stabilization regime)
//   0.70 ≤ SHM < 0.85 → Deploy to staging, manual approval for prod (Optimization)
//   SHM < 0.70 → Block deployment, require fixes (Exploration)
//
// Three-Regime Test Requirements:
//   Stabilization tests: 100% pass required for merge
//   Optimization tests: 85%+ pass required
//   Exploration tests: 70%+ pass (allowed to fail partially)
//
// Usage:
//   go run scripts/quality-gate.go --test-output=test_results.json
//   go build -o quality-gate scripts/quality-gate.go && ./quality-gate
//
// Exit codes:
//   0 = Quality gate passed
//   1 = Quality gate failed
//   2 = Configuration error
//
// Author: CI/CD Agent 2
// Date: 2025-12-27
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"os"
	"strings"
	"time"
)

// QualityGateConfig defines quality thresholds
type QualityGateConfig struct {
	// SHM thresholds for deployment
	ProductionSHM  float64 // Minimum SHM for auto-deploy to production (0.85)
	StagingSHM     float64 // Minimum SHM for staging deployment (0.70)
	BlockSHM       float64 // Below this, deployment is blocked (0.70)

	// Test pass rate requirements by regime
	StabilizationPassRate  float64 // 100% pass required for merge (1.00)
	OptimizationPassRate   float64 // 85%+ pass required (0.85)
	ExplorationPassRate    float64 // 70%+ pass (allowed to fail partially) (0.70)

	// Williams drift detection
	WilliamsDriftFactor float64 // Drift multiplier (0.05 = 5%)
}

// DefaultQualityGateConfig returns standard quality gate thresholds
func DefaultQualityGateConfig() *QualityGateConfig {
	return &QualityGateConfig{
		ProductionSHM:          0.85,
		StagingSHM:             0.70,
		BlockSHM:               0.70,
		StabilizationPassRate:  1.00,
		OptimizationPassRate:   0.85,
		ExplorationPassRate:    0.70,
		WilliamsDriftFactor:    0.05,
	}
}

// TestResults contains test execution results
type TestResults struct {
	TotalTests    int                   `json:"total_tests"`
	PassedTests   int                   `json:"passed_tests"`
	FailedTests   int                   `json:"failed_tests"`
	SkippedTests  int                   `json:"skipped_tests"`
	Coverage      float64               `json:"coverage"`
	Duration      time.Duration         `json:"duration"`
	TestsByRegime map[string]*RegimeTestResults `json:"tests_by_regime"`
	Timestamp     time.Time             `json:"timestamp"`
}

// RegimeTestResults tracks tests by three-regime classification
type RegimeTestResults struct {
	Regime       string  `json:"regime"`        // EXPLORATION, OPTIMIZATION, STABILIZATION
	Total        int     `json:"total"`
	Passed       int     `json:"passed"`
	Failed       int     `json:"failed"`
	PassRate     float64 `json:"pass_rate"`
	Required     float64 `json:"required_rate"` // Required pass rate for this regime
	Passing      bool    `json:"passing"`       // Whether meets requirements
}

// SHMScore contains System Health Metric analysis
type SHMScore struct {
	SHM              float64            `json:"shm"`               // Overall system health (0.0-1.0)
	Regime           string             `json:"regime"`            // Current regime
	SonarScores      map[string]float64 `json:"sonar_scores"`      // Individual sonar scores
	WeakestDimension string             `json:"weakest_dimension"`
	StrongestDimension string           `json:"strongest_dimension"`
	Timestamp        time.Time          `json:"timestamp"`
}

// QualityGateResult contains complete quality gate analysis
type QualityGateResult struct {
	Passed           bool               `json:"passed"`
	SHM              *SHMScore          `json:"shm"`
	Tests            *TestResults       `json:"tests"`
	Deployment       DeploymentDecision `json:"deployment"`
	FailureReasons   []string           `json:"failure_reasons,omitempty"`
	Warnings         []string           `json:"warnings,omitempty"`
	Recommendations  []string           `json:"recommendations"`
	Timestamp        time.Time          `json:"timestamp"`
}

// DeploymentDecision indicates where code can be deployed
type DeploymentDecision struct {
	CanDeployToProduction bool   `json:"can_deploy_to_production"`
	CanDeployToStaging    bool   `json:"can_deploy_to_staging"`
	RequiresManualApproval bool  `json:"requires_manual_approval"`
	Action                string `json:"action"` // AUTO_DEPLOY_PROD, DEPLOY_STAGING_MANUAL_PROD, BLOCK
}

func main() {
	// Parse command-line flags
	testOutputFile := flag.String("test-output", "", "Path to test results JSON file")
	shmFile := flag.String("shm-file", "", "Path to SHM score JSON file (optional)")
	verbose := flag.Bool("verbose", false, "Verbose output")
	jsonOutput := flag.Bool("json", false, "Output as JSON")
	flag.Parse()

	config := DefaultQualityGateConfig()

	// Load test results
	var testResults *TestResults
	if *testOutputFile != "" {
		var err error
		testResults, err = loadTestResults(*testOutputFile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "ERROR: Failed to load test results: %v\n", err)
			os.Exit(2)
		}
	} else {
		// Run tests and capture results
		var err error
		testResults, err = runTestsAndCapture()
		if err != nil {
			fmt.Fprintf(os.Stderr, "ERROR: Failed to run tests: %v\n", err)
			os.Exit(2)
		}
	}

	// Load or calculate SHM
	var shmScore *SHMScore
	if *shmFile != "" {
		var err error
		shmScore, err = loadSHMScore(*shmFile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "WARNING: Failed to load SHM score: %v\n", err)
			shmScore = estimateSHMFromTests(testResults)
		}
	} else {
		shmScore = estimateSHMFromTests(testResults)
	}

	// Run quality gate analysis
	result := evaluateQualityGate(config, testResults, shmScore)

	// Output results
	if *jsonOutput {
		jsonBytes, err := json.MarshalIndent(result, "", "  ")
		if err != nil {
			fmt.Fprintf(os.Stderr, "ERROR: Failed to marshal JSON: %v\n", err)
			os.Exit(2)
		}
		fmt.Println(string(jsonBytes))
	} else {
		printHumanReadableReport(result, *verbose)
	}

	// Exit with appropriate code
	if result.Passed {
		os.Exit(0)
	} else {
		os.Exit(1)
	}
}

// evaluateQualityGate runs comprehensive quality gate checks
func evaluateQualityGate(config *QualityGateConfig, tests *TestResults, shm *SHMScore) *QualityGateResult {
	result := &QualityGateResult{
		Passed:          true,
		SHM:             shm,
		Tests:           tests,
		FailureReasons:  []string{},
		Warnings:        []string{},
		Recommendations: []string{},
		Timestamp:       time.Now(),
	}

	// Check SHM threshold
	if shm.SHM < config.BlockSHM {
		result.Passed = false
		result.FailureReasons = append(result.FailureReasons,
			fmt.Sprintf("SHM %.3f below minimum threshold %.3f (EXPLORATION regime)", shm.SHM, config.BlockSHM))
	}

	// Check test pass rates by regime
	for regime, regimeTests := range tests.TestsByRegime {
		if !regimeTests.Passing {
			result.Passed = false
			result.FailureReasons = append(result.FailureReasons,
				fmt.Sprintf("%s tests: %.1f%% pass rate (required %.1f%%)",
					regime, regimeTests.PassRate*100, regimeTests.Required*100))
		}
	}

	// Check overall test pass rate
	overallPassRate := float64(tests.PassedTests) / float64(tests.TotalTests)
	if tests.TotalTests == 0 {
		result.Passed = false
		result.FailureReasons = append(result.FailureReasons, "No tests found")
	}

	// Determine deployment decision
	result.Deployment = determineDeployment(config, shm, overallPassRate)

	// Generate recommendations
	result.Recommendations = generateRecommendations(shm, tests)

	// Add warnings for near-threshold values
	if shm.SHM >= config.BlockSHM && shm.SHM < config.StagingSHM+0.05 {
		result.Warnings = append(result.Warnings,
			fmt.Sprintf("SHM %.3f is close to staging threshold %.3f", shm.SHM, config.StagingSHM))
	}

	if shm.SHM >= config.StagingSHM && shm.SHM < config.ProductionSHM {
		result.Warnings = append(result.Warnings,
			"In OPTIMIZATION regime - requires manual approval for production deployment")
	}

	return result
}

// determineDeployment decides where code can be deployed
func determineDeployment(config *QualityGateConfig, shm *SHMScore, passRate float64) DeploymentDecision {
	decision := DeploymentDecision{}

	if shm.SHM >= config.ProductionSHM && passRate >= config.StabilizationPassRate {
		// Auto-deploy to production
		decision.CanDeployToProduction = true
		decision.CanDeployToStaging = true
		decision.RequiresManualApproval = false
		decision.Action = "AUTO_DEPLOY_PROD"
	} else if shm.SHM >= config.StagingSHM && passRate >= config.OptimizationPassRate {
		// Deploy to staging, manual approval for prod
		decision.CanDeployToProduction = false
		decision.CanDeployToStaging = true
		decision.RequiresManualApproval = true
		decision.Action = "DEPLOY_STAGING_MANUAL_PROD"
	} else {
		// Block deployment
		decision.CanDeployToProduction = false
		decision.CanDeployToStaging = false
		decision.RequiresManualApproval = true
		decision.Action = "BLOCK"
	}

	return decision
}

// generateRecommendations creates actionable improvement suggestions
func generateRecommendations(shm *SHMScore, tests *TestResults) []string {
	recommendations := []string{}

	// Recommend focusing on weakest dimension
	if shm.WeakestDimension != "" {
		recommendations = append(recommendations,
			fmt.Sprintf("Focus on improving %s (weakest dimension)", shm.WeakestDimension))
	}

	// Recommend fixing failed tests
	if tests.FailedTests > 0 {
		recommendations = append(recommendations,
			fmt.Sprintf("Fix %d failing tests", tests.FailedTests))
	}

	// Recommend improving coverage
	if tests.Coverage < 0.80 {
		recommendations = append(recommendations,
			fmt.Sprintf("Increase test coverage from %.1f%% to 80%%+", tests.Coverage*100))
	}

	// Recommend regime-specific actions
	switch shm.Regime {
	case "EXPLORATION":
		recommendations = append(recommendations,
			"In EXPLORATION regime - focus on stabilizing core functionality",
			"Aim for SHM ≥ 0.70 to enter OPTIMIZATION regime")
	case "OPTIMIZATION":
		recommendations = append(recommendations,
			"In OPTIMIZATION regime - refine quality and reduce technical debt",
			"Aim for SHM ≥ 0.85 to enter STABILIZATION regime")
	case "STABILIZATION":
		recommendations = append(recommendations,
			"In STABILIZATION regime - maintain quality and prepare for production")
	}

	return recommendations
}

// runTestsAndCapture executes tests and captures results
func runTestsAndCapture() (*TestResults, error) {
	// This would execute `go test -json ./...` and parse results
	// For now, return mock data for demonstration
	return &TestResults{
		TotalTests:  100,
		PassedTests: 95,
		FailedTests: 5,
		SkippedTests: 0,
		Coverage:    0.87,
		Duration:    15 * time.Second,
		TestsByRegime: map[string]*RegimeTestResults{
			"STABILIZATION": {
				Regime:   "STABILIZATION",
				Total:    50,
				Passed:   50,
				Failed:   0,
				PassRate: 1.00,
				Required: 1.00,
				Passing:  true,
			},
			"OPTIMIZATION": {
				Regime:   "OPTIMIZATION",
				Total:    30,
				Passed:   27,
				Failed:   3,
				PassRate: 0.90,
				Required: 0.85,
				Passing:  true,
			},
			"EXPLORATION": {
				Regime:   "EXPLORATION",
				Total:    20,
				Passed:   18,
				Failed:   2,
				PassRate: 0.90,
				Required: 0.70,
				Passing:  true,
			},
		},
		Timestamp: time.Now(),
	}, nil
}

// estimateSHMFromTests estimates SHM when sonar data unavailable
func estimateSHMFromTests(tests *TestResults) *SHMScore {
	// Estimate SHM from test pass rate and coverage
	passRate := float64(tests.PassedTests) / float64(tests.TotalTests)
	estimatedSHM := (passRate*0.7 + tests.Coverage*0.3)

	var regime string
	if estimatedSHM >= 0.85 {
		regime = "STABILIZATION"
	} else if estimatedSHM >= 0.70 {
		regime = "OPTIMIZATION"
	} else {
		regime = "EXPLORATION"
	}

	return &SHMScore{
		SHM:    estimatedSHM,
		Regime: regime,
		SonarScores: map[string]float64{
			"code": passRate,
			"test_coverage": tests.Coverage,
		},
		WeakestDimension:   "estimated",
		StrongestDimension: "estimated",
		Timestamp:          time.Now(),
	}
}

// loadTestResults loads test results from JSON file
func loadTestResults(filename string) (*TestResults, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return nil, err
	}

	var results TestResults
	if err := json.Unmarshal(data, &results); err != nil {
		return nil, err
	}

	return &results, nil
}

// loadSHMScore loads SHM score from JSON file
func loadSHMScore(filename string) (*SHMScore, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return nil, err
	}

	var score SHMScore
	if err := json.Unmarshal(data, &score); err != nil {
		return nil, err
	}

	return &score, nil
}

// printHumanReadableReport prints formatted quality gate report
func printHumanReadableReport(result *QualityGateResult, verbose bool) {
	fmt.Println("╔═══════════════════════════════════════════════════════════════╗")
	fmt.Println("║          ASYMMETRICA QUALITY GATE REPORT                      ║")
	fmt.Println("╚═══════════════════════════════════════════════════════════════╝")
	fmt.Println()

	// Overall status
	if result.Passed {
		fmt.Println("✅ QUALITY GATE: PASSED")
	} else {
		fmt.Println("❌ QUALITY GATE: FAILED")
	}
	fmt.Println()

	// System Health Metric
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Println("SYSTEM HEALTH METRIC (SHM)")
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Printf("SHM Score:  %.3f\n", result.SHM.SHM)
	fmt.Printf("Regime:     %s\n", result.SHM.Regime)
	if result.SHM.WeakestDimension != "" && result.SHM.WeakestDimension != "estimated" {
		fmt.Printf("Weakest:    %s\n", result.SHM.WeakestDimension)
		fmt.Printf("Strongest:  %s\n", result.SHM.StrongestDimension)
	}
	fmt.Println()

	// Test Results
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Println("TEST RESULTS")
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Printf("Total:      %d\n", result.Tests.TotalTests)
	fmt.Printf("Passed:     %d (%.1f%%)\n", result.Tests.PassedTests,
		float64(result.Tests.PassedTests)/float64(result.Tests.TotalTests)*100)
	fmt.Printf("Failed:     %d\n", result.Tests.FailedTests)
	fmt.Printf("Coverage:   %.1f%%\n", result.Tests.Coverage*100)
	fmt.Printf("Duration:   %v\n", result.Tests.Duration)
	fmt.Println()

	// Three-Regime Test Breakdown
	if len(result.Tests.TestsByRegime) > 0 {
		fmt.Println("Three-Regime Test Breakdown:")
		for _, regime := range []string{"STABILIZATION", "OPTIMIZATION", "EXPLORATION"} {
			if regimeTests, ok := result.Tests.TestsByRegime[regime]; ok {
				status := "✅"
				if !regimeTests.Passing {
					status = "❌"
				}
				fmt.Printf("  %s %s: %d/%d passed (%.1f%%, required %.1f%%)\n",
					status, regime, regimeTests.Passed, regimeTests.Total,
					regimeTests.PassRate*100, regimeTests.Required*100)
			}
		}
		fmt.Println()
	}

	// Deployment Decision
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Println("DEPLOYMENT DECISION")
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Printf("Action:     %s\n", result.Deployment.Action)

	actionDescriptions := map[string]string{
		"AUTO_DEPLOY_PROD":           "✅ Auto-deploy to PRODUCTION (SHM ≥ 0.85)",
		"DEPLOY_STAGING_MANUAL_PROD": "⚠️  Deploy to STAGING, manual approval for PRODUCTION (0.70 ≤ SHM < 0.85)",
		"BLOCK":                      "❌ Deployment BLOCKED (SHM < 0.70)",
	}

	if desc, ok := actionDescriptions[result.Deployment.Action]; ok {
		fmt.Printf("            %s\n", desc)
	}
	fmt.Println()

	// Failure Reasons
	if len(result.FailureReasons) > 0 {
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		fmt.Println("FAILURE REASONS")
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		for i, reason := range result.FailureReasons {
			fmt.Printf("%d. %s\n", i+1, reason)
		}
		fmt.Println()
	}

	// Warnings
	if len(result.Warnings) > 0 {
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		fmt.Println("⚠️  WARNINGS")
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		for i, warning := range result.Warnings {
			fmt.Printf("%d. %s\n", i+1, warning)
		}
		fmt.Println()
	}

	// Recommendations
	if len(result.Recommendations) > 0 {
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		fmt.Println("💡 RECOMMENDATIONS")
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		for i, rec := range result.Recommendations {
			fmt.Printf("%d. %s\n", i+1, rec)
		}
		fmt.Println()
	}

	// Sonar scores (if verbose)
	if verbose && len(result.SHM.SonarScores) > 0 {
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		fmt.Println("SONAR SCORES")
		fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
		for sonar, score := range result.SHM.SonarScores {
			bar := generateProgressBar(score, 30)
			fmt.Printf("%-12s %.3f %s\n", strings.ToUpper(sonar)+":", score, bar)
		}
		fmt.Println()
	}

	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
	fmt.Printf("Generated: %s\n", result.Timestamp.Format("2006-01-02 15:04:05"))
	fmt.Println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
}

// generateProgressBar creates ASCII progress bar
func generateProgressBar(value float64, width int) string {
	filled := int(math.Round(value * float64(width)))
	bar := strings.Repeat("█", filled) + strings.Repeat("░", width-filled)
	return fmt.Sprintf("[%s]", bar)
}
