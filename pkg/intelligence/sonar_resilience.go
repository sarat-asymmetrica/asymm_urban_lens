// Package intelligence implements resilient sonar execution
//
// Mission: Handle partial sonar failure gracefully (Margaret Hamilton Standard)
//
// "The system must work even when components fail."
// - Margaret Hamilton (Apollo 11 Flight Software Lead)
//
// Philosophy:
// - Sonars can fail (network, disk, timeout, bugs)
// - Partial data is better than no data
// - Confidence degrades gracefully with missing sonars
// - Health reports guide debugging
//
// Author: Zen Gardener (Resilience Engineering)
// Date: 2025-12-27
package intelligence

import (
	"context"
	"fmt"
	"sync"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/intelligence/sonars"
)

// SonarResult captures individual sonar execution outcome
//
// Philosophy: Every sonar execution has 4 outcomes:
// 1. Success: score + report available
// 2. Partial success: score available, report degraded
// 3. Failure: error captured, sonar unhealthy
// 4. Timeout: context cancelled
type SonarResult struct {
	SonarName string                // Which sonar (UX, Design, Code, etc.)
	Score     float64               // Quality score (0.0-1.0, 0.0 if failed)
	Error     error                 // Error if sonar failed
	Timestamp time.Time             // When sonar completed
	Duration  time.Duration         // How long sonar took
	Healthy   bool                  // true = success, false = failed
	Report    *sonars.Report        // Full report (nil if failed)
	Telemetry *sonars.TelemetryData // Raw telemetry (nil if PING failed)
	Metrics   *sonars.Metrics       // Processed metrics (nil if ECHO failed)
}

// HealthReport provides comprehensive system health analysis
type HealthReport struct {
	TotalSonars     int                      // Total sonars attempted
	HealthySonars   int                      // Sonars that succeeded
	UnhealthySonars int                      // Sonars that failed
	HealthyNames    []string                 // Names of healthy sonars
	UnhealthyNames  []string                 // Names of failed sonars
	Failures        map[string]error         // Failure reasons by sonar
	Recommendations []string                 // Recommended actions
	Confidence      float64                  // Overall confidence (0.0-1.0)
	Timestamp       time.Time                // When report generated
	SeverityLevel   HealthSeverity           // CRITICAL, WARNING, OK, EXCELLENT
	PartialData     bool                     // true if some sonars failed
	Results         map[string]*SonarResult  // All sonar results
}

// HealthSeverity indicates system health severity
type HealthSeverity string

const (
	HealthCritical  HealthSeverity = "CRITICAL"  // All or most sonars failed
	HealthWarning   HealthSeverity = "WARNING"   // Some sonars failed
	HealthOK        HealthSeverity = "OK"        // All sonars succeeded but scores low
	HealthExcellent HealthSeverity = "EXCELLENT" // All sonars succeeded, scores high
)

// RunSonarsWithResilience executes all sonars in parallel with graceful degradation
//
// Philosophy (Margaret Hamilton):
// - Run all sonars concurrently (don't let one slow down others)
// - Capture all errors (don't let one failure crash the system)
// - Timeout individual sonars (don't let one hang forever)
// - Return partial results (some data > no data)
//
// Returns:
// - results: slice of all sonar results (healthy + unhealthy)
// - error: only if ALL sonars failed (0/6 healthy)
func RunSonarsWithResilience(ctx context.Context, sonarEngines []sonars.SonarEngine, app *sonars.AppState) ([]SonarResult, error) {
	// Execute all sonars in parallel
	results := make([]SonarResult, len(sonarEngines))
	var wg sync.WaitGroup
	wg.Add(len(sonarEngines))

	for i, sonar := range sonarEngines {
		go func(index int, engine sonars.SonarEngine) {
			defer wg.Done()
			results[index] = executeSonarSafely(ctx, engine, app)
		}(i, sonar)
	}

	// Wait for all sonars to complete (or timeout)
	wg.Wait()

	// Check if ALL sonars failed
	healthyCount := 0
	for _, result := range results {
		if result.Healthy {
			healthyCount++
		}
	}

	if healthyCount == 0 {
		return results, fmt.Errorf("CRITICAL: All sonars failed (0/%d healthy)", len(results))
	}

	return results, nil
}

// RunSonarsWithResilienceFromCalculator is a convenience wrapper for SHMCalculator
func RunSonarsWithResilienceFromCalculator(ctx context.Context, calculator *SHMCalculator, app *sonars.AppState) ([]SonarResult, error) {
	// Extract sonar engines as interfaces
	sonarEngines := []sonars.SonarEngine{
		calculator.uxSonar,
		calculator.designSonar,
		calculator.codeSonar,
		calculator.semanticSonar,
		calculator.journeySonar,
		calculator.stateSonar,
	}

	return RunSonarsWithResilience(ctx, sonarEngines, app)
}

// executeSonarSafely wraps sonar execution with panic recovery and timeout
//
// Philosophy:
// - Recover from panics (sonar bugs shouldn't crash system)
// - Respect context timeout (don't hang forever)
// - Capture detailed error info (debugging)
func executeSonarSafely(ctx context.Context, sonar sonars.SonarEngine, app *sonars.AppState) (result SonarResult) {
	startTime := time.Now()

	// Single defer for ALL panic recovery (runs on ANY panic or normal return)
	defer func() {
		if r := recover(); r != nil {
			// Panic occurred - populate error and ensure basics are set
			result.Error = fmt.Errorf("PANIC: %v", r)
			result.Healthy = false
			result.Duration = time.Since(startTime)
			result.Timestamp = time.Now()

			// Try to get sonar name if not already set
			if result.SonarName == "" {
				defer func() {
					if r2 := recover(); r2 != nil {
						result.SonarName = "Unknown Sonar (name() panicked)"
					}
				}()
				result.SonarName = sonar.Name()
			}
		}
	}()

	// Get sonar name first (might panic)
	result.SonarName = sonar.Name()
	result.Timestamp = time.Now()
	result.Healthy = false
	result.Score = 0.0

	// Execute full sonar cycle
	fullResult, err := sonars.ExecuteFullSonar(ctx, sonar, app)
	result.Duration = time.Since(startTime)

	if err != nil {
		result.Error = err
		result.Healthy = false
		return
	}

	// Success - populate result
	result.Healthy = true
	result.Score = fullResult.Score
	result.Report = fullResult.Report
	result.Telemetry = fullResult.Telemetry
	result.Metrics = fullResult.Metrics

	return
}

// CalculateSHMWithPartialData computes SHM from partial sonar results
//
// Formula:
//   SHM = Σ(healthy_score × weight) / Σ(healthy_weights)
//   confidence = healthy_count / total_count
//
// Philosophy:
// - Use only healthy sonars for calculation
// - Renormalize weights (if UX fails, redistribute its 25% weight)
// - Confidence decreases linearly with missing sonars
//
// Returns:
// - shm: System Health Metric (0.0-1.0)
// - confidence: How reliable is this SHM? (0.0-1.0)
// - error: Only if < 1 healthy sonar (can't calculate meaningful SHM)
func CalculateSHMWithPartialData(results []SonarResult) (float64, float64, error) {
	// Weights from research (UX + Design = 50%, internal = 50%)
	weights := map[string]float64{
		"UX Sonar":       0.25,  // User-facing (25%)
		"Design Sonar":   0.25,  // User-facing (25%)
		"Code Sonar":     0.125, // Internal quality (12.5%)
		"Semantic Sonar": 0.125, // Internal quality (12.5%)
		"Journey Sonar":  0.125, // Internal quality (12.5%)
		"State Sonar":    0.125, // Internal quality (12.5%)
	}

	// Collect healthy sonar scores
	healthyScores := make(map[string]float64)
	totalHealthy := 0

	for _, result := range results {
		if result.Healthy {
			healthyScores[result.SonarName] = result.Score
			totalHealthy++
		}
	}

	// Need at least 1 healthy sonar
	if totalHealthy == 0 {
		return 0.0, 0.0, fmt.Errorf("cannot calculate SHM: 0/%d sonars healthy", len(results))
	}

	// Calculate weighted average (renormalized)
	weightedSum := 0.0
	totalWeight := 0.0

	for sonarName, score := range healthyScores {
		weight := weights[sonarName]
		weightedSum += score * weight
		totalWeight += weight
	}

	shm := weightedSum / totalWeight

	// Calculate confidence (linear degradation)
	totalSonars := len(results)
	confidence := float64(totalHealthy) / float64(totalSonars)

	return shm, confidence, nil
}

// GetHealthReport generates comprehensive health analysis
//
// Philosophy:
// - Tell the truth (don't hide failures)
// - Guide debugging (actionable recommendations)
// - Prioritize severity (what needs fixing first?)
func GetHealthReport(results []SonarResult) HealthReport {
	report := HealthReport{
		TotalSonars:    len(results),
		HealthySonars:  0,
		UnhealthySonars: 0,
		HealthyNames:   []string{},
		UnhealthyNames: []string{},
		Failures:       make(map[string]error),
		Recommendations: []string{},
		Timestamp:      time.Now(),
		PartialData:    false,
		Results:        make(map[string]*SonarResult),
	}

	// Analyze each sonar
	for _, result := range results {
		// Copy result to map
		resultCopy := result
		report.Results[result.SonarName] = &resultCopy

		if result.Healthy {
			report.HealthySonars++
			report.HealthyNames = append(report.HealthyNames, result.SonarName)
		} else {
			report.UnhealthySonars++
			report.UnhealthyNames = append(report.UnhealthyNames, result.SonarName)
			report.Failures[result.SonarName] = result.Error
			report.PartialData = true
		}
	}

	// Calculate confidence
	if report.TotalSonars > 0 {
		report.Confidence = float64(report.HealthySonars) / float64(report.TotalSonars)
	}

	// Determine severity
	report.SeverityLevel = determineSeverity(report.Confidence)

	// Generate recommendations
	report.Recommendations = generateRecommendations(report)

	return report
}

// determineSeverity maps confidence to severity level
//
// Thresholds (Hamilton Standard):
// - 100% healthy (6/6) = EXCELLENT
// - 83%+ healthy (5/6) = OK (can trust SHM)
// - 50%+ healthy (3/6) = WARNING (partial trust)
// - <50% healthy (<3/6) = CRITICAL (don't trust SHM)
func determineSeverity(confidence float64) HealthSeverity {
	switch {
	case confidence >= 1.0:
		return HealthExcellent
	case confidence >= 0.83: // 5/6 sonars
		return HealthOK
	case confidence >= 0.50: // 3/6 sonars
		return HealthWarning
	default:
		return HealthCritical
	}
}

// generateRecommendations creates actionable debugging steps
func generateRecommendations(report HealthReport) []string {
	recommendations := []string{}

	// Critical: Most sonars failed
	if report.Confidence < 0.50 {
		recommendations = append(recommendations,
			"URGENT: More than half of sonars failed - system health unknown",
			"Check application state (is it running? accessible?)",
			"Review logs for common errors across failed sonars",
		)
	}

	// Warning: Some sonars failed
	if report.Confidence >= 0.50 && report.Confidence < 1.0 {
		recommendations = append(recommendations,
			fmt.Sprintf("Partial data available (%d/%d sonars healthy)", report.HealthySonars, report.TotalSonars),
			"Review failed sonars individually for specific issues",
		)
	}

	// Specific sonar failures
	for sonarName, err := range report.Failures {
		recommendations = append(recommendations,
			fmt.Sprintf("%s failed: %v", sonarName, err),
		)
	}

	// Prioritize fixes (user-facing sonars more critical)
	for _, name := range []string{"UX Sonar", "Design Sonar"} {
		if _, failed := report.Failures[name]; failed {
			recommendations = append(recommendations,
				fmt.Sprintf("PRIORITY: Fix %s (user-facing, 25%% weight)", name),
			)
		}
	}

	// If all healthy, celebrate
	if report.Confidence == 1.0 {
		recommendations = append(recommendations,
			"All sonars healthy - full system visibility available",
		)
	}

	return recommendations
}

// FormatHealthReport generates human-readable health dashboard
func FormatHealthReport(report HealthReport) string {
	dashboard := "\n"
	dashboard += "┌─────────────────────────────────────────────────────────────┐\n"
	dashboard += "│              SONAR HEALTH REPORT (RESILIENCE)               │\n"
	dashboard += "└─────────────────────────────────────────────────────────────┘\n"
	dashboard += "\n"

	// Overall health
	dashboard += fmt.Sprintf("⚡ Overall Health: %s\n", report.SeverityLevel)
	dashboard += fmt.Sprintf("📊 Confidence: %.1f%% (%d/%d sonars healthy)\n",
		report.Confidence*100.0, report.HealthySonars, report.TotalSonars)
	dashboard += fmt.Sprintf("⏱️  Generated: %v\n", report.Timestamp.Format("15:04:05"))
	dashboard += "\n"

	// Healthy sonars
	if len(report.HealthyNames) > 0 {
		dashboard += "✅ Healthy Sonars:\n"
		for _, name := range report.HealthyNames {
			result := report.Results[name]
			dashboard += fmt.Sprintf("   • %s (%.3f score, %v duration)\n",
				name, result.Score, result.Duration)
		}
		dashboard += "\n"
	}

	// Failed sonars
	if len(report.UnhealthyNames) > 0 {
		dashboard += "❌ Failed Sonars:\n"
		for _, name := range report.UnhealthyNames {
			err := report.Failures[name]
			dashboard += fmt.Sprintf("   • %s: %v\n", name, err)
		}
		dashboard += "\n"
	}

	// Recommendations
	if len(report.Recommendations) > 0 {
		dashboard += "🔧 Recommendations:\n"
		for i, rec := range report.Recommendations {
			dashboard += fmt.Sprintf("   %d. %s\n", i+1, rec)
		}
		dashboard += "\n"
	}

	// Severity guide
	dashboard += "Severity Guide:\n"
	dashboard += "  • EXCELLENT (100%): All sonars healthy - full visibility\n"
	dashboard += "  • OK (83%+):        5+ sonars healthy - trust SHM\n"
	dashboard += "  • WARNING (50%+):   3+ sonars healthy - partial trust\n"
	dashboard += "  • CRITICAL (<50%):  <3 sonars healthy - don't trust SHM\n"
	dashboard += "\n"

	return dashboard
}
