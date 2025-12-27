// Package intelligence resilience tests
//
// Testing philosophy (Hamilton Standard):
// - Test happy path (all sonars healthy)
// - Test degradation (some sonars fail)
// - Test critical failure (all sonars fail)
// - Test confidence calculation (mathematical correctness)
// - Test panic recovery (sonar bugs don't crash system)
// - Test timeout handling (context cancellation)
package intelligence

import (
	"context"
	"errors"
	"fmt"
	"testing"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/intelligence/sonars"
)

// mockSonar simulates a sonar engine with configurable behavior
type mockSonar struct {
	name        string
	shouldFail  bool
	shouldPanic bool
	shouldHang  bool
	score       float64
	delay       time.Duration
}

func (m *mockSonar) Name() string {
	return m.name
}

func (m *mockSonar) Ping(ctx context.Context, app *sonars.AppState) (*sonars.TelemetryData, error) {
	// Simulate delay
	if m.delay > 0 {
		time.Sleep(m.delay)
	}

	// Simulate hang (wait for context cancellation)
	if m.shouldHang {
		<-ctx.Done()
		return nil, ctx.Err()
	}

	// Simulate panic
	if m.shouldPanic {
		panic("mock sonar panic!")
	}

	// Simulate failure
	if m.shouldFail {
		return nil, errors.New("mock sonar ping failed")
	}

	return &sonars.TelemetryData{
		SonarName:   m.name,
		CollectedAt: time.Now(),
		RawData:     map[string]interface{}{"test": "data"},
		Duration:    m.delay,
	}, nil
}

func (m *mockSonar) Echo(ctx context.Context, telemetry *sonars.TelemetryData) (*sonars.Metrics, error) {
	if m.shouldFail {
		return nil, errors.New("mock sonar echo failed")
	}

	return &sonars.Metrics{
		SonarName: m.name,
		Values:    map[string]float64{"test": m.score},
		Details:   map[string]interface{}{},
		Timestamp: time.Now(),
	}, nil
}

func (m *mockSonar) Map(ctx context.Context, metrics *sonars.Metrics) float64 {
	return m.score
}

func (m *mockSonar) Critique(ctx context.Context, score float64, metrics *sonars.Metrics) *sonars.Report {
	return &sonars.Report{
		SonarName:       m.name,
		Score:           score,
		Status:          sonars.DetermineStatus(score),
		Summary:         fmt.Sprintf("Mock sonar score: %.3f", score),
		Findings:        []sonars.Finding{},
		Recommendations: []string{},
		Timestamp:       time.Now(),
	}
}

// TestAllSonarsHealthy tests the happy path (6/6 sonars succeed)
func TestAllSonarsHealthy(t *testing.T) {
	// Create 6 healthy mock sonars
	sonarEngines := []sonars.SonarEngine{
		&mockSonar{name: "UX Sonar", score: 0.90},
		&mockSonar{name: "Design Sonar", score: 0.85},
		&mockSonar{name: "Code Sonar", score: 0.80},
		&mockSonar{name: "Semantic Sonar", score: 0.88},
		&mockSonar{name: "Journey Sonar", score: 0.92},
		&mockSonar{name: "State Sonar", score: 0.87},
	}

	app := &sonars.AppState{
		RootPath: "/test/app",
		AppType:  "TestApp",
	}

	ctx := context.Background()

	// Run sonars with resilience
	results, err := RunSonarsWithResilience(ctx, sonarEngines, app)

	// Should succeed (not return error)
	if err != nil {
		t.Fatalf("Expected no error, got: %v", err)
	}

	// Should have 6 results
	if len(results) != 6 {
		t.Fatalf("Expected 6 results, got %d", len(results))
	}

	// All should be healthy
	healthyCount := 0
	for _, result := range results {
		if result.Healthy {
			healthyCount++
		}
	}

	if healthyCount != 6 {
		t.Fatalf("Expected 6 healthy sonars, got %d", healthyCount)
	}

	// Calculate SHM with partial data
	shm, confidence, err := CalculateSHMWithPartialData(results)
	if err != nil {
		t.Fatalf("Expected no error calculating SHM, got: %v", err)
	}

	// Confidence should be 1.0 (100%)
	if confidence != 1.0 {
		t.Errorf("Expected confidence 1.0, got %.3f", confidence)
	}

	// SHM should be > 0.8 (all scores are high)
	if shm < 0.8 {
		t.Errorf("Expected SHM > 0.8, got %.3f", shm)
	}

	// Health report
	report := GetHealthReport(results)

	if report.SeverityLevel != HealthExcellent {
		t.Errorf("Expected EXCELLENT severity, got %s", report.SeverityLevel)
	}

	if report.HealthySonars != 6 {
		t.Errorf("Expected 6 healthy sonars, got %d", report.HealthySonars)
	}

	if report.UnhealthySonars != 0 {
		t.Errorf("Expected 0 unhealthy sonars, got %d", report.UnhealthySonars)
	}

	t.Logf("✅ All sonars healthy test passed")
	t.Logf("   SHM: %.3f, Confidence: %.3f", shm, confidence)
	t.Logf("   Health: %s", report.SeverityLevel)
}

// TestSomeSonarsFail tests partial degradation (3/6 sonars fail)
func TestSomeSonarsFail(t *testing.T) {
	// Create mix of healthy and failing sonars
	sonarEngines := []sonars.SonarEngine{
		&mockSonar{name: "UX Sonar", score: 0.90},           // Healthy
		&mockSonar{name: "Design Sonar", score: 0.85},       // Healthy
		&mockSonar{name: "Code Sonar", score: 0.80},         // Healthy
		&mockSonar{name: "Semantic Sonar", shouldFail: true}, // FAIL
		&mockSonar{name: "Journey Sonar", shouldFail: true},  // FAIL
		&mockSonar{name: "State Sonar", shouldFail: true},    // FAIL
	}

	app := &sonars.AppState{
		RootPath: "/test/app",
		AppType:  "TestApp",
	}

	ctx := context.Background()

	// Run sonars with resilience
	results, err := RunSonarsWithResilience(ctx, sonarEngines, app)

	// Should NOT error (partial data is OK)
	if err != nil {
		t.Fatalf("Expected no error with partial data, got: %v", err)
	}

	// Should have 6 results
	if len(results) != 6 {
		t.Fatalf("Expected 6 results, got %d", len(results))
	}

	// Count healthy
	healthyCount := 0
	unhealthyCount := 0
	for _, result := range results {
		if result.Healthy {
			healthyCount++
		} else {
			unhealthyCount++
		}
	}

	if healthyCount != 3 {
		t.Fatalf("Expected 3 healthy sonars, got %d", healthyCount)
	}

	if unhealthyCount != 3 {
		t.Fatalf("Expected 3 unhealthy sonars, got %d", unhealthyCount)
	}

	// Calculate SHM with partial data
	shm, confidence, err := CalculateSHMWithPartialData(results)
	if err != nil {
		t.Fatalf("Expected no error with partial data, got: %v", err)
	}

	// Confidence should be 0.5 (50% = 3/6)
	if confidence != 0.5 {
		t.Errorf("Expected confidence 0.5, got %.3f", confidence)
	}

	// SHM should still be calculable (using only healthy sonars)
	if shm == 0.0 {
		t.Errorf("Expected non-zero SHM from healthy sonars, got 0.0")
	}

	// Health report
	report := GetHealthReport(results)

	if report.SeverityLevel != HealthWarning {
		t.Errorf("Expected WARNING severity, got %s", report.SeverityLevel)
	}

	if report.PartialData != true {
		t.Errorf("Expected partial data flag to be true")
	}

	if len(report.Failures) != 3 {
		t.Errorf("Expected 3 failures recorded, got %d", len(report.Failures))
	}

	t.Logf("✅ Some sonars fail test passed")
	t.Logf("   SHM: %.3f, Confidence: %.3f", shm, confidence)
	t.Logf("   Health: %s (partial data)", report.SeverityLevel)
}

// TestAllSonarsFail tests critical failure (0/6 sonars succeed)
func TestAllSonarsFail(t *testing.T) {
	// Create all failing sonars
	sonarEngines := []sonars.SonarEngine{
		&mockSonar{name: "UX Sonar", shouldFail: true},
		&mockSonar{name: "Design Sonar", shouldFail: true},
		&mockSonar{name: "Code Sonar", shouldFail: true},
		&mockSonar{name: "Semantic Sonar", shouldFail: true},
		&mockSonar{name: "Journey Sonar", shouldFail: true},
		&mockSonar{name: "State Sonar", shouldFail: true},
	}

	app := &sonars.AppState{
		RootPath: "/test/app",
		AppType:  "TestApp",
	}

	ctx := context.Background()

	// Run sonars with resilience
	results, err := RunSonarsWithResilience(ctx, sonarEngines, app)

	// SHOULD error (all failed)
	if err == nil {
		t.Fatalf("Expected error when all sonars fail, got nil")
	}

	// Should have 6 results (even though all failed)
	if len(results) != 6 {
		t.Fatalf("Expected 6 results, got %d", len(results))
	}

	// All should be unhealthy
	healthyCount := 0
	for _, result := range results {
		if result.Healthy {
			healthyCount++
		}
	}

	if healthyCount != 0 {
		t.Fatalf("Expected 0 healthy sonars, got %d", healthyCount)
	}

	// Calculate SHM should fail
	_, _, err = CalculateSHMWithPartialData(results)
	if err == nil {
		t.Fatalf("Expected error calculating SHM with 0 healthy sonars, got nil")
	}

	// Health report
	report := GetHealthReport(results)

	if report.SeverityLevel != HealthCritical {
		t.Errorf("Expected CRITICAL severity, got %s", report.SeverityLevel)
	}

	if report.Confidence != 0.0 {
		t.Errorf("Expected confidence 0.0, got %.3f", report.Confidence)
	}

	t.Logf("✅ All sonars fail test passed")
	t.Logf("   Confidence: %.3f (CRITICAL)", report.Confidence)
	t.Logf("   All %d sonars failed as expected", len(results))
}

// TestConfidenceCalculation tests mathematical correctness of confidence
func TestConfidenceCalculation(t *testing.T) {
	testCases := []struct {
		name             string
		healthyCount     int
		totalCount       int
		expectedConfidence float64
		expectedSeverity HealthSeverity
	}{
		{"6/6 healthy", 6, 6, 1.00, HealthExcellent},
		{"5/6 healthy", 5, 6, 0.833, HealthOK},
		{"4/6 healthy", 4, 6, 0.667, HealthWarning}, // 66.7% is below 83% threshold
		{"3/6 healthy", 3, 6, 0.50, HealthWarning},
		{"2/6 healthy", 2, 6, 0.333, HealthCritical},
		{"1/6 healthy", 1, 6, 0.167, HealthCritical},
		{"0/6 healthy", 0, 6, 0.00, HealthCritical},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Create mock results
			results := []SonarResult{}
			for i := 0; i < tc.totalCount; i++ {
				result := SonarResult{
					SonarName: fmt.Sprintf("Sonar %d", i+1),
					Healthy:   i < tc.healthyCount,
					Score:     0.85,
					Timestamp: time.Now(),
				}
				results = append(results, result)
			}

			// Calculate SHM (if possible)
			if tc.healthyCount > 0 {
				shm, confidence, err := CalculateSHMWithPartialData(results)
				if err != nil {
					t.Fatalf("Expected no error, got: %v", err)
				}

				// Check confidence (allow 0.01 tolerance for floating point)
				if absResilience(confidence-tc.expectedConfidence) > 0.01 {
					t.Errorf("Expected confidence %.3f, got %.3f", tc.expectedConfidence, confidence)
				}

				// SHM should be reasonable (using healthy sonars)
				if shm == 0.0 {
					t.Errorf("Expected non-zero SHM, got 0.0")
				}
			} else {
				// Should error with 0 healthy
				_, _, err := CalculateSHMWithPartialData(results)
				if err == nil {
					t.Errorf("Expected error with 0 healthy sonars, got nil")
				}
			}

			// Check severity level
			report := GetHealthReport(results)
			if report.SeverityLevel != tc.expectedSeverity {
				t.Errorf("Expected severity %s, got %s", tc.expectedSeverity, report.SeverityLevel)
			}

			t.Logf("   ✅ %s: confidence %.3f, severity %s",
				tc.name, tc.expectedConfidence, tc.expectedSeverity)
		})
	}
}

// TestPanicRecovery tests that panicking sonars don't crash the system
func TestPanicRecovery(t *testing.T) {
	// Create sonar that panics
	sonarEngines := []sonars.SonarEngine{
		&mockSonar{name: "UX Sonar", shouldPanic: true}, // PANIC
		&mockSonar{name: "Design Sonar", score: 0.85},   // Healthy
		&mockSonar{name: "Code Sonar", score: 0.80},     // Healthy
		&mockSonar{name: "Semantic Sonar", score: 0.88}, // Healthy
		&mockSonar{name: "Journey Sonar", score: 0.92},  // Healthy
		&mockSonar{name: "State Sonar", score: 0.87},    // Healthy
	}

	app := &sonars.AppState{
		RootPath: "/test/app",
		AppType:  "TestApp",
	}

	ctx := context.Background()

	// Run sonars - should NOT crash despite panic
	results, err := RunSonarsWithResilience(ctx, sonarEngines, app)

	// Should succeed (panic caught)
	if err != nil {
		t.Fatalf("Expected no error despite panic, got: %v", err)
	}

	// Find UX Sonar result (use index to avoid pointer to loop variable)
	var uxResult *SonarResult
	for i := range results {
		if results[i].SonarName == "UX Sonar" {
			uxResult = &results[i]
			break
		}
	}

	if uxResult == nil {
		t.Fatalf("UX Sonar result not found in %d results", len(results))
	}

	// Should be unhealthy
	if uxResult.Healthy {
		t.Errorf("Expected UX Sonar to be unhealthy after panic")
	}

	// Should have panic error
	if uxResult.Error == nil {
		t.Errorf("Expected panic error to be captured")
	}

	// Other sonars should still be healthy
	healthyCount := 0
	for _, result := range results {
		if result.Healthy {
			healthyCount++
		}
	}

	if healthyCount != 5 {
		t.Errorf("Expected 5 healthy sonars, got %d", healthyCount)
	}

	t.Logf("✅ Panic recovery test passed")
	t.Logf("   Panic caught: %v", uxResult.Error)
	t.Logf("   Other sonars unaffected: %d/5 healthy", healthyCount)
}

// TestTimeoutHandling tests context cancellation
func TestTimeoutHandling(t *testing.T) {
	// Create sonar that hangs
	sonarEngines := []sonars.SonarEngine{
		&mockSonar{name: "UX Sonar", shouldHang: true},                                       // HANG
		&mockSonar{name: "Design Sonar", score: 0.85, delay: 10 * time.Millisecond},
		&mockSonar{name: "Code Sonar", score: 0.80, delay: 10 * time.Millisecond},
		&mockSonar{name: "Semantic Sonar", score: 0.88, delay: 10 * time.Millisecond},
		&mockSonar{name: "Journey Sonar", score: 0.92, delay: 10 * time.Millisecond},
		&mockSonar{name: "State Sonar", score: 0.87, delay: 10 * time.Millisecond},
	}

	app := &sonars.AppState{
		RootPath: "/test/app",
		AppType:  "TestApp",
	}

	// Create context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	// Run sonars - should timeout UX Sonar
	results, err := RunSonarsWithResilience(ctx, sonarEngines, app)

	// Should succeed (timeout caught)
	if err != nil {
		t.Fatalf("Expected no error despite timeout, got: %v", err)
	}

	// Find UX Sonar result (use index to avoid pointer to loop variable)
	var uxResult *SonarResult
	for i := range results {
		if results[i].SonarName == "UX Sonar" {
			uxResult = &results[i]
			break
		}
	}

	if uxResult == nil {
		t.Fatalf("UX Sonar result not found")
	}

	// Should be unhealthy (timeout)
	if uxResult.Healthy {
		t.Errorf("Expected UX Sonar to be unhealthy after timeout")
	}

	// Other sonars should complete (fast enough)
	healthyCount := 0
	for _, result := range results {
		if result.Healthy {
			healthyCount++
		}
	}

	// At least 4 should complete (UX hangs, some might timeout)
	if healthyCount < 4 {
		t.Errorf("Expected at least 4 healthy sonars, got %d", healthyCount)
	}

	t.Logf("✅ Timeout handling test passed")
	t.Logf("   Timeout caught: %v", uxResult.Error)
	t.Logf("   Fast sonars completed: %d/5", healthyCount)
}

// TestFormatHealthReport tests dashboard generation
func TestFormatHealthReport(t *testing.T) {
	// Create mix of healthy and failing sonars
	results := []SonarResult{
		{SonarName: "UX Sonar", Healthy: true, Score: 0.90, Duration: 50 * time.Millisecond},
		{SonarName: "Design Sonar", Healthy: true, Score: 0.85, Duration: 40 * time.Millisecond},
		{SonarName: "Code Sonar", Healthy: false, Error: errors.New("test error"), Duration: 30 * time.Millisecond},
		{SonarName: "Semantic Sonar", Healthy: true, Score: 0.88, Duration: 45 * time.Millisecond},
		{SonarName: "Journey Sonar", Healthy: false, Error: errors.New("another error"), Duration: 20 * time.Millisecond},
		{SonarName: "State Sonar", Healthy: true, Score: 0.87, Duration: 35 * time.Millisecond},
	}

	report := GetHealthReport(results)
	dashboard := FormatHealthReport(report)

	// Should contain key sections
	if !containsResilience(dashboard, "SONAR HEALTH REPORT") {
		t.Errorf("Dashboard missing header")
	}

	if !containsResilience(dashboard, "Overall Health") {
		t.Errorf("Dashboard missing overall health")
	}

	if !containsResilience(dashboard, "Healthy Sonars") {
		t.Errorf("Dashboard missing healthy sonars section")
	}

	if !containsResilience(dashboard, "Failed Sonars") {
		t.Errorf("Dashboard missing failed sonars section")
	}

	if !containsResilience(dashboard, "Recommendations") {
		t.Errorf("Dashboard missing recommendations section")
	}

	if !containsResilience(dashboard, "Severity Guide") {
		t.Errorf("Dashboard missing severity guide")
	}

	t.Logf("✅ Format health report test passed")
	t.Logf("\n%s", dashboard)
}

// Helper functions

func absResilience(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}

func containsResilience(s, substr string) bool {
	// Simple substring check
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
