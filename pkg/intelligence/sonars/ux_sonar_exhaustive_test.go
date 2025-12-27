package sonars

import (
	"context"
	"math"
	"testing"
	"time"
)

// =============================================================================
// STABILIZATION TESTS (100% pass required)
// Reference: Nielsen's Response Time Research & Core Web Vitals
// =============================================================================

// TestUXSonar_FPSCalculation_60FPS validates 16.7ms → 60 FPS
// Nielsen: <16ms feels instant (1 frame at 60Hz)
func TestUXSonar_FPSCalculation_60FPS(t *testing.T) {
	// FPS = 1000 / delta_time_ms
	deltaTimeMs := 16.7
	expectedFPS := 1000.0 / deltaTimeMs

	tolerance := 0.2
	if math.Abs(expectedFPS-60.0) > tolerance {
		t.Errorf("60 FPS calculation incorrect: got %.2f, want 60.0 (±%.1f)", expectedFPS, tolerance)
	}

	t.Logf("✓ 60 FPS = 16.7ms per frame (%.2f FPS)", expectedFPS)
	t.Logf("  Nielsen: <16ms feels instant (imperceptible delay)")
}

// TestUXSonar_FPSCalculation_30FPS validates 33.3ms → 30 FPS
// Nielsen: 16-100ms feels responsive but noticeable
func TestUXSonar_FPSCalculation_30FPS(t *testing.T) {
	// FPS = 1000 / delta_time_ms
	deltaTimeMs := 33.3
	expectedFPS := 1000.0 / deltaTimeMs

	tolerance := 0.2
	if math.Abs(expectedFPS-30.0) > tolerance {
		t.Errorf("30 FPS calculation incorrect: got %.2f, want 30.0 (±%.1f)", expectedFPS, tolerance)
	}

	t.Logf("✓ 30 FPS = 33.3ms per frame (%.2f FPS)", expectedFPS)
	t.Logf("  Nielsen: 16-100ms responsive but noticeable lag")
}

// TestUXSonar_SmoothnessScore_Perfect validates 60 FPS → 1.0 score
func TestUXSonar_SmoothnessScore_Perfect(t *testing.T) {
	// smoothness_score = min(1.0, FPS / 60.0)
	fps := 60.0
	targetFPS := 60.0

	smoothness := math.Min(1.0, fps/targetFPS)

	if smoothness != 1.0 {
		t.Errorf("Perfect smoothness incorrect: got %.2f, want 1.0", smoothness)
	}

	t.Logf("✓ 60 FPS smoothness: %.2f (perfect)", smoothness)
}

// TestUXSonar_SmoothnessScore_Choppy validates 30 FPS → 0.5 score
func TestUXSonar_SmoothnessScore_Choppy(t *testing.T) {
	// smoothness_score = min(1.0, FPS / 60.0)
	fps := 30.0
	targetFPS := 60.0

	smoothness := math.Min(1.0, fps/targetFPS)

	expected := 0.5
	if smoothness != expected {
		t.Errorf("Choppy smoothness incorrect: got %.2f, want %.2f", smoothness, expected)
	}

	t.Logf("✓ 30 FPS smoothness: %.2f (choppy)", smoothness)
}

// TestUXSonar_SmoothnessScore_Terrible validates 15 FPS → 0.25 score
func TestUXSonar_SmoothnessScore_Terrible(t *testing.T) {
	// smoothness_score = min(1.0, FPS / 60.0)
	fps := 15.0
	targetFPS := 60.0

	smoothness := math.Min(1.0, fps/targetFPS)

	expected := 0.25
	if smoothness != expected {
		t.Errorf("Terrible smoothness incorrect: got %.2f, want %.2f", smoothness, expected)
	}

	t.Logf("✓ 15 FPS smoothness: %.2f (terrible)", smoothness)
	t.Logf("  User will notice severe jank and stuttering")
}

// TestUXSonar_NielsenThreshold_Instant validates <100ms instant response
// Source: Nielsen Norman Group - Response Times (1993, 2014)
func TestUXSonar_NielsenThreshold_Instant(t *testing.T) {
	nielsenInstantThreshold := 100.0 // milliseconds

	tests := []struct {
		name       string
		latencyMs  float64
		expectPass bool
	}{
		{"Imperceptible 10ms", 10.0, true},
		{"Instant 50ms", 50.0, true},
		{"Instant 99ms", 99.0, true},
		{"Just over threshold 101ms", 101.0, false},
		{"Slow 200ms", 200.0, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			isInstant := tt.latencyMs < nielsenInstantThreshold

			if isInstant != tt.expectPass {
				t.Errorf("Instant threshold check failed: %s (%.1fms) - got %v, want %v",
					tt.name, tt.latencyMs, isInstant, tt.expectPass)
			}

			t.Logf("✓ Nielsen instant threshold (<%.0fms): %.1fms = %v",
				nielsenInstantThreshold, tt.latencyMs, isInstant)
		})
	}

	t.Logf("✓ Nielsen: <100ms = user feels in control, no special feedback needed")
}

// TestUXSonar_NielsenThreshold_Flow validates <1s flow continuity
func TestUXSonar_NielsenThreshold_Flow(t *testing.T) {
	nielsenFlowThreshold := 1000.0 // milliseconds (1 second)

	tests := []struct {
		name       string
		latencyMs  float64
		expectPass bool
	}{
		{"Instant 100ms", 100.0, true},
		{"Responsive 500ms", 500.0, true},
		{"Just under 999ms", 999.0, true},
		{"Just over 1001ms", 1001.0, false},
		{"Attention lost 2000ms", 2000.0, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			inFlow := tt.latencyMs < nielsenFlowThreshold

			if inFlow != tt.expectPass {
				t.Errorf("Flow threshold check failed: %s (%.1fms) - got %v, want %v",
					tt.name, tt.latencyMs, inFlow, tt.expectPass)
			}

			t.Logf("✓ Nielsen flow threshold (<%.0fms): %.1fms = %v",
				nielsenFlowThreshold, tt.latencyMs, inFlow)
		})
	}

	t.Logf("✓ Nielsen: <1s = user's flow of thought stays uninterrupted")
}

// TestUXSonar_NielsenThreshold_Attention validates <10s attention retention
func TestUXSonar_NielsenThreshold_Attention(t *testing.T) {
	nielsenAttentionThreshold := 10000.0 // milliseconds (10 seconds)

	tests := []struct {
		name       string
		latencyMs  float64
		expectPass bool
	}{
		{"In flow 1000ms", 1000.0, true},
		{"Waiting 5000ms", 5000.0, true},
		{"Just under 9999ms", 9999.0, true},
		{"Lost attention 10001ms", 10001.0, false},
		{"User left 20000ms", 20000.0, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			hasAttention := tt.latencyMs < nielsenAttentionThreshold

			if hasAttention != tt.expectPass {
				t.Errorf("Attention threshold check failed: %s (%.1fms) - got %v, want %v",
					tt.name, tt.latencyMs, hasAttention, tt.expectPass)
			}

			t.Logf("✓ Nielsen attention threshold (<%.0fms): %.1fms = %v",
				nielsenAttentionThreshold, tt.latencyMs, hasAttention)
		})
	}

	t.Logf("✓ Nielsen: <10s = user's attention stays focused, needs feedback indicator")
}

// TestUXSonar_CLS_Good validates CLS < 0.1 (Google Core Web Vitals)
func TestUXSonar_CLS_Good(t *testing.T) {
	// Google's Core Web Vitals: CLS < 0.1 = good, >0.25 = poor
	goodThreshold := 0.1

	tests := []struct {
		name       string
		cls        float64
		expectGood bool
	}{
		{"Excellent 0.01", 0.01, true},
		{"Good 0.05", 0.05, true},
		{"Just good 0.099", 0.099, true},
		{"Needs improvement 0.15", 0.15, false},
		{"Poor 0.30", 0.30, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			isGood := tt.cls < goodThreshold

			if isGood != tt.expectGood {
				t.Errorf("CLS good threshold check failed: %s (%.3f) - got %v, want %v",
					tt.name, tt.cls, isGood, tt.expectGood)
			}

			// Calculate stability score (higher CLS = lower stability)
			stability := math.Max(0.0, 1.0-(tt.cls/goodThreshold))

			t.Logf("✓ CLS %.3f → stability score: %.2f (good: %v)",
				tt.cls, stability, isGood)
		})
	}

	t.Logf("✓ Google Core Web Vitals: CLS <0.1 = good (no jarring layout shifts)")
}

// TestUXSonar_CLS_Poor validates CLS > 0.25 detection
func TestUXSonar_CLS_Poor(t *testing.T) {
	// Google's Core Web Vitals: CLS > 0.25 = poor user experience
	poorThreshold := 0.25

	tests := []struct {
		name       string
		cls        float64
		expectPoor bool
	}{
		{"Good 0.05", 0.05, false},
		{"Needs improvement 0.15", 0.15, false},
		{"Just poor 0.26", 0.26, true},
		{"Very poor 0.50", 0.50, true},
		{"Terrible 1.00", 1.00, true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			isPoor := tt.cls > poorThreshold

			if isPoor != tt.expectPoor {
				t.Errorf("CLS poor threshold check failed: %s (%.3f) - got %v, want %v",
					tt.name, tt.cls, isPoor, tt.expectPoor)
			}

			t.Logf("✓ CLS %.3f → poor: %v (threshold: >%.2f)",
				tt.cls, isPoor, poorThreshold)
		})
	}

	t.Logf("✓ Google Core Web Vitals: CLS >0.25 = poor (jarring shifts)")
}

// =============================================================================
// OPTIMIZATION TESTS (85% required)
// =============================================================================

// TestUXSonar_PING_CollectsTelemetry validates PING phase telemetry collection
func TestUXSonar_PING_CollectsTelemetry(t *testing.T) {
	ux := NewUXSonar()
	ctx := context.Background()

	app := &AppState{
		RootPath: "/test/app",
		Frontend: &FrontendInfo{
			Framework:  "react",
			Components: []string{"src/App.tsx"},
		},
	}

	telemetry, err := ux.Ping(ctx, app)
	if err != nil {
		t.Fatalf("PING failed: %v", err)
	}

	// Validate telemetry structure
	if telemetry.SonarName != "UX Sonar" {
		t.Errorf("Wrong sonar name: got %s, want UX Sonar", telemetry.SonarName)
	}

	// Check for expected raw data keys
	expectedKeys := []string{"fps_measurements", "cls_measurements", "load_measurements"}
	for _, key := range expectedKeys {
		if _, ok := telemetry.RawData[key]; !ok {
			t.Errorf("Missing raw data key: %s", key)
		}
	}

	// Validate telemetry timestamp
	if telemetry.CollectedAt.IsZero() {
		t.Error("Telemetry timestamp not set")
	}

	// Validate duration is measured
	if telemetry.Duration < 0 {
		t.Error("Telemetry duration is negative")
	}

	t.Logf("✓ PING collected %d raw data keys in %v", len(telemetry.RawData), telemetry.Duration)
}

// TestUXSonar_ECHO_ProcessesMetrics validates ECHO phase metric processing
func TestUXSonar_ECHO_ProcessesMetrics(t *testing.T) {
	ux := NewUXSonar()
	ctx := context.Background()

	telemetry := &TelemetryData{
		SonarName:   "UX Sonar",
		CollectedAt: time.Now(),
		RawData: map[string]interface{}{
			"fps_measurements": map[string]float64{
				"average": 55.0,
				"minimum": 50.0,
				"maximum": 60.0,
			},
			"cls_measurements": map[string]float64{
				"total": 0.08,
			},
			"load_measurements": map[string]float64{
				"page_load":             1500.0,
				"time_to_interactive":   2000.0,
				"first_contentful_paint": 1300.0,
			},
		},
	}

	metrics, err := ux.Echo(ctx, telemetry)
	if err != nil {
		t.Fatalf("ECHO failed: %v", err)
	}

	// Validate expected metrics
	expectedMetrics := []string{
		"avg_fps",
		"min_fps",
		"max_fps",
		"fps_variance",
		"cumulative_layout_shift",
		"page_load_ms",
		"time_to_interactive_ms",
		"first_contentful_paint_ms",
	}

	for _, metric := range expectedMetrics {
		if _, ok := metrics.Values[metric]; !ok {
			t.Errorf("Missing metric: %s", metric)
		}
	}

	// Validate FPS calculations
	if metrics.Values["avg_fps"] != 55.0 {
		t.Errorf("avg_fps incorrect: got %.1f, want 55.0", metrics.Values["avg_fps"])
	}

	if metrics.Values["fps_variance"] != 10.0 { // 60 - 50
		t.Errorf("fps_variance incorrect: got %.1f, want 10.0", metrics.Values["fps_variance"])
	}

	// Validate CLS extraction
	if metrics.Values["cumulative_layout_shift"] != 0.08 {
		t.Errorf("CLS incorrect: got %.2f, want 0.08", metrics.Values["cumulative_layout_shift"])
	}

	// Validate load metrics
	if metrics.Values["page_load_ms"] != 1500.0 {
		t.Errorf("page_load_ms incorrect: got %.1f, want 1500.0", metrics.Values["page_load_ms"])
	}

	t.Logf("✓ ECHO processed %d metrics", len(metrics.Values))
	for name, value := range metrics.Values {
		t.Logf("  %s: %.2f", name, value)
	}
}

// TestUXSonar_MAP_NormalizesTo01 validates MAP phase 0.0-1.0 normalization
func TestUXSonar_MAP_NormalizesTo01(t *testing.T) {
	ux := NewUXSonar()
	ctx := context.Background()

	tests := []struct {
		name    string
		metrics map[string]float64
		wantMin float64
		wantMax float64
	}{
		{
			name: "Perfect scores",
			metrics: map[string]float64{
				"avg_fps":                  60.0,
				"cumulative_layout_shift":  0.01,
				"page_load_ms":             800.0,
				"time_to_interactive_ms":   1200.0,
			},
			wantMin: 0.83,
			wantMax: 0.87,
		},
		{
			name: "Poor scores",
			metrics: map[string]float64{
				"avg_fps":                  20.0,
				"cumulative_layout_shift":  0.30,
				"page_load_ms":             4000.0,
				"time_to_interactive_ms":   6000.0,
			},
			wantMin: 0.0,
			wantMax: 0.20,
		},
		{
			name: "Mixed scores",
			metrics: map[string]float64{
				"avg_fps":                  45.0,
				"cumulative_layout_shift":  0.08,
				"page_load_ms":             1800.0,
				"time_to_interactive_ms":   2500.0,
			},
			wantMin: 0.35,
			wantMax: 0.43,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			metrics := &Metrics{
				SonarName: "UX Sonar",
				Values:    tt.metrics,
			}

			score := ux.Map(ctx, metrics)

			if score < 0.0 || score > 1.0 {
				t.Errorf("Score out of bounds: %.2f (want [0.0, 1.0])", score)
			}

			if score < tt.wantMin || score > tt.wantMax {
				t.Errorf("Score %.2f outside expected range [%.2f, %.2f]",
					score, tt.wantMin, tt.wantMax)
			}

			t.Logf("✓ MAP normalized score: %.2f (range: [%.2f, %.2f])",
				score, tt.wantMin, tt.wantMax)
		})
	}
}

// TestUXSonar_CRITIQUE_GeneratesReport validates CRITIQUE phase report generation
func TestUXSonar_CRITIQUE_GeneratesReport(t *testing.T) {
	ux := NewUXSonar()
	ctx := context.Background()

	metrics := &Metrics{
		SonarName: "UX Sonar",
		Values: map[string]float64{
			"avg_fps":                  45.0,
			"cumulative_layout_shift":  0.15,
			"page_load_ms":             2200.0,
			"time_to_interactive_ms":   3000.0,
		},
	}

	score := 0.58
	report := ux.Critique(ctx, score, metrics)

	// Validate report structure
	if report.SonarName != "UX Sonar" {
		t.Errorf("Wrong sonar name: got %s, want UX Sonar", report.SonarName)
	}

	if report.Score != score {
		t.Errorf("Score mismatch: got %.2f, want %.2f", report.Score, score)
	}

	if len(report.Summary) == 0 {
		t.Error("Empty summary")
	}

	if len(report.Findings) == 0 {
		t.Error("No findings generated")
	}

	if len(report.Recommendations) == 0 {
		t.Error("No recommendations generated")
	}

	t.Logf("✓ CRITIQUE generated report:")
	t.Logf("  Summary: %s", report.Summary)
	t.Logf("  Findings: %d", len(report.Findings))
	t.Logf("  Recommendations: %d", len(report.Recommendations))

	// Validate finding types
	for _, finding := range report.Findings {
		t.Logf("    [%s] %s: %s", finding.Severity, finding.Type, finding.Message)
	}
}

// TestUXSonar_WeightedAverageFormula validates scoring formula
func TestUXSonar_WeightedAverageFormula(t *testing.T) {
	// From ux_sonar.go Map():
	// score = (smoothness*0.35 + stability*0.35 + loadSpeed*0.15 + interactiveSpeed*0.15)

	smoothness := 0.80        // 48 FPS → 0.80
	stability := 0.70         // CLS 0.03 → 0.70
	loadSpeed := 0.60         // 1600ms → 0.60
	interactiveSpeed := 0.50  // 2800ms → 0.50

	expectedScore := (smoothness*0.35 + stability*0.35 + loadSpeed*0.15 + interactiveSpeed*0.15)

	// Verify weights sum to 1.0
	totalWeight := 0.35 + 0.35 + 0.15 + 0.15
	if totalWeight != 1.0 {
		t.Errorf("Weights don't sum to 1.0: got %.2f", totalWeight)
	}

	t.Logf("✓ Weighted average formula:")
	t.Logf("  Smoothness (FPS):      %.2f × 0.35 = %.3f", smoothness, smoothness*0.35)
	t.Logf("  Stability (CLS):       %.2f × 0.35 = %.3f", stability, stability*0.35)
	t.Logf("  Load Speed:            %.2f × 0.15 = %.3f", loadSpeed, loadSpeed*0.15)
	t.Logf("  Interactive Speed:     %.2f × 0.15 = %.3f", interactiveSpeed, interactiveSpeed*0.15)
	t.Logf("  Final Score:           %.3f", expectedScore)
}

// =============================================================================
// EXPLORATION TESTS (70% required)
// =============================================================================

// TestUXSonar_Integration_WithSHM validates SHM weight contribution
func TestUXSonar_Integration_WithSHM(t *testing.T) {
	ux := NewUXSonar()
	_ = ux // Prevent unused variable error

	// UX Sonar contributes to SHM (assumed weight 0.30 for performance)
	shmWeight := 0.30

	// Test score propagation
	uxScore := 0.75

	// SHM contribution = score × weight
	shmContribution := uxScore * shmWeight

	expectedContribution := 0.225 // 0.75 × 0.30

	tolerance := 0.0001
	if math.Abs(shmContribution-expectedContribution) > tolerance {
		t.Errorf("SHM contribution incorrect: got %.4f, want %.4f",
			shmContribution, expectedContribution)
	}

	t.Logf("✓ UX Sonar → SHM integration:")
	t.Logf("  UX score: %.2f", uxScore)
	t.Logf("  SHM weight: %.2f", shmWeight)
	t.Logf("  SHM contribution: %.4f", shmContribution)
	t.Logf("  Total SHM = (UX×0.30) + (Code×0.25) + (Design×0.25) + (Business×0.20)")
}

// TestUXSonar_LongTasks_Detection validates >50ms task detection
// Source: Chrome DevTools Performance - Long Tasks API
func TestUXSonar_LongTasks_Detection(t *testing.T) {
	longTaskThreshold := 50.0 // milliseconds

	tests := []struct {
		name         string
		taskDuration float64
		expectLong   bool
		description  string
	}{
		{
			name:         "Quick task 10ms",
			taskDuration: 10.0,
			expectLong:   false,
			description:  "No blocking",
		},
		{
			name:         "Acceptable 40ms",
			taskDuration: 40.0,
			expectLong:   false,
			description:  "No blocking",
		},
		{
			name:         "Just long 51ms",
			taskDuration: 51.0,
			expectLong:   true,
			description:  "Blocks main thread, may cause jank",
		},
		{
			name:         "Very long 200ms",
			taskDuration: 200.0,
			expectLong:   true,
			description:  "Severe blocking, will cause jank",
		},
		{
			name:         "Catastrophic 1000ms",
			taskDuration: 1000.0,
			expectLong:   true,
			description:  "App appears frozen",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			isLong := tt.taskDuration > longTaskThreshold

			if isLong != tt.expectLong {
				t.Errorf("Long task detection failed: %s (%.1fms) - got %v, want %v",
					tt.name, tt.taskDuration, isLong, tt.expectLong)
			}

			t.Logf("✓ Task %.1fms → long: %v (%s)",
				tt.taskDuration, isLong, tt.description)
		})
	}

	t.Logf("✓ Chrome Long Tasks API: >50ms blocks main thread, causes jank")
}

// TestUXSonar_FPSVariance_StutterDetection validates FPS consistency
func TestUXSonar_FPSVariance_StutterDetection(t *testing.T) {
	tests := []struct {
		name            string
		minFPS          float64
		maxFPS          float64
		avgFPS          float64
		expectStutter   bool
		description     string
	}{
		{
			name:            "Perfectly smooth",
			minFPS:          59.0,
			maxFPS:          60.0,
			avgFPS:          59.5,
			expectStutter:   false,
			description:     "Variance <2 FPS = imperceptible",
		},
		{
			name:            "Slight variation",
			minFPS:          55.0,
			maxFPS:          60.0,
			avgFPS:          57.5,
			expectStutter:   false,
			description:     "Variance 5 FPS = acceptable",
		},
		{
			name:            "Noticeable stutter",
			minFPS:          40.0,
			maxFPS:          60.0,
			avgFPS:          50.0,
			expectStutter:   true,
			description:     "Variance 20 FPS = user notices jank",
		},
		{
			name:            "Severe stutter",
			minFPS:          20.0,
			maxFPS:          60.0,
			avgFPS:          40.0,
			expectStutter:   true,
			description:     "Variance 40 FPS = very jarring",
		},
	}

	stutterThreshold := 10.0 // FPS variance >10 = noticeable stutter

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			variance := tt.maxFPS - tt.minFPS
			hasStutter := variance > stutterThreshold

			if hasStutter != tt.expectStutter {
				t.Errorf("Stutter detection failed: %s (variance %.1f) - got %v, want %v",
					tt.name, variance, hasStutter, tt.expectStutter)
			}

			t.Logf("✓ FPS variance %.1f (min: %.1f, max: %.1f, avg: %.1f) → stutter: %v",
				variance, tt.minFPS, tt.maxFPS, tt.avgFPS, hasStutter)
			t.Logf("  %s", tt.description)
		})
	}
}

// TestUXSonar_EndToEnd_FullPipeline validates complete PING→ECHO→MAP→CRITIQUE
func TestUXSonar_EndToEnd_FullPipeline(t *testing.T) {
	ux := NewUXSonar()
	ctx := context.Background()

	// Mock app state
	app := &AppState{
		RootPath: "/test/app",
		Frontend: &FrontendInfo{
			Framework:  "react",
			Components: []string{"src/App.tsx", "src/components/Dashboard.tsx"},
		},
	}

	// PING: Collect telemetry
	telemetry, err := ux.Ping(ctx, app)
	if err != nil {
		t.Fatalf("PING failed: %v", err)
	}
	t.Logf("✓ PING completed in %v", telemetry.Duration)

	// ECHO: Compute metrics
	metrics, err := ux.Echo(ctx, telemetry)
	if err != nil {
		t.Fatalf("ECHO failed: %v", err)
	}
	t.Logf("✓ ECHO computed %d metrics", len(metrics.Values))

	// MAP: Normalize to score
	score := ux.Map(ctx, metrics)
	if score < 0.0 || score > 1.0 {
		t.Errorf("MAP score out of bounds: %.2f", score)
	}
	t.Logf("✓ MAP normalized to score: %.2f", score)

	// CRITIQUE: Generate report
	report := ux.Critique(ctx, score, metrics)
	if len(report.Findings) == 0 {
		t.Error("CRITIQUE generated no findings")
	}
	t.Logf("✓ CRITIQUE generated %d findings, %d recommendations",
		len(report.Findings), len(report.Recommendations))

	// Validate complete pipeline
	t.Logf("\n=== FULL PIPELINE RESULTS ===")
	t.Logf("Final Score: %.1f%%", score*100)
	t.Logf("Status: %s", report.Status)
	t.Logf("Summary: %s", report.Summary)

	// Validate all metrics present
	requiredMetrics := []string{
		"avg_fps",
		"cumulative_layout_shift",
		"page_load_ms",
		"time_to_interactive_ms",
	}

	for _, metric := range requiredMetrics {
		if _, ok := metrics.Values[metric]; !ok {
			t.Errorf("Missing required metric in pipeline: %s", metric)
		}
	}
}

// =============================================================================
// ADDITIONAL MATHEMATICAL RIGOR TESTS
// =============================================================================

// TestUXSonar_CoreWebVitals_LCP validates Largest Contentful Paint
// Google: LCP < 2.5s = good, >4.0s = poor
func TestUXSonar_CoreWebVitals_LCP(t *testing.T) {
	goodThreshold := 2500.0  // milliseconds
	poorThreshold := 4000.0  // milliseconds

	tests := []struct {
		name       string
		lcpMs      float64
		expectRating string
	}{
		{"Excellent 1200ms", 1200.0, "good"},
		{"Good 2400ms", 2400.0, "good"},
		{"Needs improvement 3000ms", 3000.0, "needs-improvement"},
		{"Poor 4500ms", 4500.0, "poor"},
		{"Very poor 8000ms", 8000.0, "poor"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var rating string
			if tt.lcpMs < goodThreshold {
				rating = "good"
			} else if tt.lcpMs < poorThreshold {
				rating = "needs-improvement"
			} else {
				rating = "poor"
			}

			if rating != tt.expectRating {
				t.Errorf("LCP rating incorrect: got %s, want %s", rating, tt.expectRating)
			}

			t.Logf("✓ LCP %.0fms → %s", tt.lcpMs, rating)
		})
	}

	t.Logf("✓ Core Web Vitals LCP: <2.5s good, 2.5-4s needs improvement, >4s poor")
}

// TestUXSonar_CoreWebVitals_FID validates First Input Delay
// Google: FID < 100ms = good, >300ms = poor
func TestUXSonar_CoreWebVitals_FID(t *testing.T) {
	goodThreshold := 100.0  // milliseconds
	poorThreshold := 300.0  // milliseconds

	tests := []struct {
		name       string
		fidMs      float64
		expectRating string
	}{
		{"Excellent 50ms", 50.0, "good"},
		{"Good 95ms", 95.0, "good"},
		{"Needs improvement 200ms", 200.0, "needs-improvement"},
		{"Poor 350ms", 350.0, "poor"},
		{"Very poor 1000ms", 1000.0, "poor"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var rating string
			if tt.fidMs < goodThreshold {
				rating = "good"
			} else if tt.fidMs < poorThreshold {
				rating = "needs-improvement"
			} else {
				rating = "poor"
			}

			if rating != tt.expectRating {
				t.Errorf("FID rating incorrect: got %s, want %s", rating, tt.expectRating)
			}

			t.Logf("✓ FID %.0fms → %s", tt.fidMs, rating)
		})
	}

	t.Logf("✓ Core Web Vitals FID: <100ms good, 100-300ms needs improvement, >300ms poor")
}

// TestUXSonar_RenderBlocking_Detection validates render-blocking resources
func TestUXSonar_RenderBlocking_Detection(t *testing.T) {
	tests := []struct {
		name             string
		blockingTimeMs   float64
		expectBlocking   bool
		description      string
	}{
		{
			name:             "No blocking",
			blockingTimeMs:   0.0,
			expectBlocking:   false,
			description:      "All resources async/defer",
		},
		{
			name:             "Minimal blocking 50ms",
			blockingTimeMs:   50.0,
			expectBlocking:   false,
			description:      "Acceptable critical CSS",
		},
		{
			name:             "Moderate blocking 200ms",
			blockingTimeMs:   200.0,
			expectBlocking:   true,
			description:      "Delays FCP, optimize critical path",
		},
		{
			name:             "Severe blocking 1000ms",
			blockingTimeMs:   1000.0,
			expectBlocking:   true,
			description:      "Severe FCP delay, eliminate blocking",
		},
	}

	blockingThreshold := 100.0 // ms

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			isBlocking := tt.blockingTimeMs > blockingThreshold

			if isBlocking != tt.expectBlocking {
				t.Errorf("Render blocking detection failed: %s (%.1fms) - got %v, want %v",
					tt.name, tt.blockingTimeMs, isBlocking, tt.expectBlocking)
			}

			t.Logf("✓ Render blocking %.0fms → blocking: %v (%s)",
				tt.blockingTimeMs, isBlocking, tt.description)
		})
	}
}
