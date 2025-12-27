package intelligence_test

import (
	"context"
	"fmt"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/intelligence"
	"github.com/asymmetrica/urbanlens/pkg/intelligence/sonars"
)

// Example showing how to use sonar resilience in production
func ExampleRunSonarsWithResilience() {
	// Create SHM calculator with all 6 sonars
	calculator := intelligence.NewSHMCalculator()

	// Create application state
	app := &sonars.AppState{
		RootPath: "/path/to/app",
		AppType:  "WebApp",
		Frontend: &sonars.FrontendInfo{
			Framework:  "react",
			EntryPoint: "src/App.tsx",
			Components: []string{"src/components/Header.tsx", "src/components/Footer.tsx"},
		},
		Backend: &sonars.BackendInfo{
			Language:   "go",
			EntryPoint: "main.go",
			Handlers:   []string{"handlers/api.go", "handlers/auth.go"},
		},
	}

	// Create context with timeout (prevent hanging forever)
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// Run sonars with resilience
	results, err := intelligence.RunSonarsWithResilienceFromCalculator(ctx, calculator, app)

	if err != nil {
		// All sonars failed - critical system failure
		fmt.Printf("CRITICAL: All sonars failed: %v\n", err)
		return
	}

	// Calculate SHM with partial data
	shm, confidence, err := intelligence.CalculateSHMWithPartialData(results)
	if err != nil {
		fmt.Printf("ERROR: Cannot calculate SHM: %v\n", err)
		return
	}

	// Get health report
	report := intelligence.GetHealthReport(results)

	// Display results
	fmt.Printf("System Health Metric: %.3f\n", shm)
	fmt.Printf("Confidence: %.1f%% (%d/%d sonars healthy)\n",
		confidence*100.0, report.HealthySonars, report.TotalSonars)
	fmt.Printf("Overall Health: %s\n", report.SeverityLevel)

	// Show dashboard
	dashboard := intelligence.FormatHealthReport(report)
	fmt.Println(dashboard)

	// Decision making based on confidence
	switch report.SeverityLevel {
	case intelligence.HealthExcellent:
		fmt.Println("✅ All systems operational - full confidence in metrics")
	case intelligence.HealthOK:
		fmt.Println("✅ Most systems operational - trust metrics with minor caveats")
	case intelligence.HealthWarning:
		fmt.Println("⚠️  Partial system failure - review failed sonars before trusting metrics")
	case intelligence.HealthCritical:
		fmt.Println("❌ Major system failure - do not trust metrics, investigate immediately")
	}
}

// Example showing how to handle specific sonar failures
func ExampleGetHealthReport() {
	// Simulated results (in real code, these come from RunSonarsWithResilience)
	results := []intelligence.SonarResult{
		{
			SonarName: "UX Sonar",
			Healthy:   true,
			Score:     0.92,
			Duration:  120 * time.Millisecond,
		},
		{
			SonarName: "Design Sonar",
			Healthy:   false,
			Error:     fmt.Errorf("network timeout"),
			Duration:  5 * time.Second,
		},
		{
			SonarName: "Code Sonar",
			Healthy:   true,
			Score:     0.85,
			Duration:  200 * time.Millisecond,
		},
		{
			SonarName: "Semantic Sonar",
			Healthy:   true,
			Score:     0.88,
			Duration:  150 * time.Millisecond,
		},
		{
			SonarName: "Journey Sonar",
			Healthy:   false,
			Error:     fmt.Errorf("PANIC: unexpected nil pointer"),
			Duration:  10 * time.Millisecond,
		},
		{
			SonarName: "State Sonar",
			Healthy:   true,
			Score:     0.90,
			Duration:  180 * time.Millisecond,
		},
	}

	// Generate health report
	report := intelligence.GetHealthReport(results)

	// Analyze failures
	fmt.Printf("Health Status: %s\n", report.SeverityLevel)
	fmt.Printf("Confidence: %.1f%%\n\n", report.Confidence*100.0)

	// Handle each failure specifically
	for _, name := range report.UnhealthyNames {
		err := report.Failures[name]
		fmt.Printf("Failed: %s\n", name)
		fmt.Printf("  Reason: %v\n", err)

		// Specific remediation based on failure type
		switch name {
		case "Design Sonar":
			fmt.Println("  Action: Check network connectivity to design analysis service")
		case "Journey Sonar":
			fmt.Println("  Action: Review journey sonar logs, likely code bug")
		}
		fmt.Println()
	}

	// Recommendations
	fmt.Println("Recommendations:")
	for i, rec := range report.Recommendations {
		fmt.Printf("  %d. %s\n", i+1, rec)
	}
}

// Example showing confidence-based decision making
func ExampleCalculateSHMWithPartialData() {
	// Simulated results with varying health
	results := []intelligence.SonarResult{
		{SonarName: "UX Sonar", Healthy: true, Score: 0.90},
		{SonarName: "Design Sonar", Healthy: true, Score: 0.85},
		{SonarName: "Code Sonar", Healthy: false, Error: fmt.Errorf("failed")},
		{SonarName: "Semantic Sonar", Healthy: false, Error: fmt.Errorf("failed")},
		{SonarName: "Journey Sonar", Healthy: false, Error: fmt.Errorf("failed")},
		{SonarName: "State Sonar", Healthy: true, Score: 0.88},
	}

	// Calculate SHM with partial data
	shm, confidence, err := intelligence.CalculateSHMWithPartialData(results)

	if err != nil {
		fmt.Printf("Cannot calculate SHM: %v\n", err)
		return
	}

	fmt.Printf("SHM: %.3f (from %d healthy sonars)\n", shm, 3)
	fmt.Printf("Confidence: %.1f%% (3/6 sonars)\n\n", confidence*100.0)

	// Decision making based on confidence
	if confidence >= 0.83 {
		// 5+ sonars healthy (83%+)
		fmt.Println("HIGH CONFIDENCE: Trust SHM for production decisions")
		fmt.Printf("  → Safe to deploy if SHM >= 0.85\n")
	} else if confidence >= 0.50 {
		// 3-4 sonars healthy (50-83%)
		fmt.Println("MEDIUM CONFIDENCE: Use SHM with caution")
		fmt.Printf("  → Review failed sonars before critical decisions\n")
		fmt.Printf("  → Consider running manual checks\n")
	} else {
		// <3 sonars healthy (<50%)
		fmt.Println("LOW CONFIDENCE: Do not trust SHM")
		fmt.Printf("  → Fix sonar failures before making decisions\n")
		fmt.Printf("  → System health is unknown\n")
	}

	// Output:
	// SHM: 0.876 (from 3 healthy sonars)
	// Confidence: 50.0% (3/6 sonars)
	//
	// MEDIUM CONFIDENCE: Use SHM with caution
	//   → Review failed sonars before critical decisions
	//   → Consider running manual checks
}
