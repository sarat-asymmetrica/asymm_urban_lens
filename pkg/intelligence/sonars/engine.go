// Package sonars implements the Unified Intelligence Monitoring Sonar Suite
//
// Six Sonar Engines following PING → ECHO → MAP → CRITIQUE pattern:
// 1. UX Sonar: Performance mechanics (FPS, CLS, smoothness)
// 2. Design Sonar: Beauty mechanics (contrast, harmony, balance)
// 3. Code Sonar: Engine mechanics (complexity, duplication, cohesion)
// 4. Semantic Sonar: Data flow mechanics (dependencies, modularity)
// 5. Journey Sonar: Navigation mechanics (frustration, rage clicks)
// 6. State Sonar: Complexity mechanics (SMT, state explosion)
//
// Discovered by: Dr. Yuki Tanaka (Cognitive Psychology), Marcus Chen (Performance),
//                Aria Rodriguez (UI/UX Design)
// Research: UNIFIED_INTELLIGENCE_MONITORING_RESEARCH_PAPER.html
// Date: 2025-11-07
package sonars

import (
	"context"
	"time"
)

// SonarEngine is the universal interface for all 6 sonars
//
// PING → ECHO → MAP → CRITIQUE is inspired by actual sonar:
//   PING: Send signal into environment (collect telemetry)
//   ECHO: Receive reflection (process raw data into metrics)
//   MAP: Normalize signal (convert to 0.0-1.0 quality score)
//   CRITIQUE: Interpret results (generate human-readable report)
type SonarEngine interface {
	// Ping collects raw telemetry data from the app
	Ping(ctx context.Context, app *AppState) (*TelemetryData, error)

	// Echo processes telemetry into metrics
	Echo(ctx context.Context, telemetry *TelemetryData) (*Metrics, error)

	// Map normalizes metrics to 0.0-1.0 quality score
	Map(ctx context.Context, metrics *Metrics) float64

	// Critique generates human-readable report with recommendations
	Critique(ctx context.Context, score float64, metrics *Metrics) *Report

	// Name returns the sonar engine name (e.g., "UX Sonar", "Design Sonar")
	Name() string
}

// AppState represents the generated app being analyzed
type AppState struct {
	RootPath      string            // Root directory of generated app
	AppType       string            // App type (TodoApp, FileShareApp, etc.)
	Components    []string          // List of component files
	Backend       *BackendInfo      // Backend service info
	Frontend      *FrontendInfo     // Frontend service info
	Database      *DatabaseInfo     // Database schema info
	Configuration map[string]string // App configuration
}

// BackendInfo contains backend service details
type BackendInfo struct {
	Language    string   // go, rust, python, etc.
	EntryPoint  string   // main.go, main.rs, etc.
	APIEndpoints int     // Number of API endpoints
	Handlers    []string // List of handler files
}

// FrontendInfo contains frontend service details
type FrontendInfo struct {
	Framework  string   // react, svelte, vue, etc.
	EntryPoint string   // App.tsx, main.svelte, etc.
	Components []string // List of component files
	Routes     []string // List of route paths
}

// DatabaseInfo contains database schema details
type DatabaseInfo struct {
	Type      string   // postgres, sqlite, mysql, etc.
	SchemaFile string   // schema.sql, schema.prisma, etc.
	Tables    []string // List of table names
}

// TelemetryData is raw data collected during PING phase
type TelemetryData struct {
	SonarName   string                 // Which sonar collected this
	CollectedAt time.Time              // When data was collected
	RawData     map[string]interface{} // Raw telemetry (sonar-specific)
	Duration    time.Duration          // Collection duration
}

// Metrics are processed measurements from ECHO phase
type Metrics struct {
	SonarName string                 // Which sonar computed these
	Values    map[string]float64     // Named metric values
	Details   map[string]interface{} // Additional details
	Timestamp time.Time              // When metrics were computed
}

// Report is the human-readable critique from CRITIQUE phase
type Report struct {
	SonarName       string         // Which sonar generated this
	Score           float64        // Overall quality score (0.0-1.0)
	Status          StatusLevel    // Critical, Warning, OK, Excellent
	Summary         string         // One-line summary
	Findings        []Finding      // Detailed findings
	Recommendations []string       // Actionable recommendations
	Timestamp       time.Time      // When report was generated
	Duration        time.Duration  // Total sonar execution time
}

// StatusLevel indicates sonar health status
type StatusLevel string

const (
	StatusCritical  StatusLevel = "CRITICAL"  // SHM < 0.50 (system broken)
	StatusWarning   StatusLevel = "WARNING"   // SHM 0.50-0.70 (needs attention)
	StatusOK        StatusLevel = "OK"        // SHM 0.70-0.85 (acceptable)
	StatusExcellent StatusLevel = "EXCELLENT" // SHM ≥ 0.85 (production ready)
)

// Finding is a specific observation from sonar analysis
type Finding struct {
	Type     FindingType // Issue, Praise, Observation
	Severity string      // Critical, High, Medium, Low, Info
	Message  string      // Human-readable description
	Location string      // File/component where finding occurred
	Value    float64     // Measured value (if applicable)
	Target   float64     // Target/threshold value (if applicable)
}

// FindingType categorizes findings
type FindingType string

const (
	FindingIssue       FindingType = "ISSUE"       // Something wrong
	FindingPraise      FindingType = "PRAISE"      // Something excellent
	FindingObservation FindingType = "OBSERVATION" // Neutral fact
)

// SonarResult bundles all outputs from a complete sonar run
type SonarResult struct {
	Telemetry *TelemetryData // PING output
	Metrics   *Metrics       // ECHO output
	Score     float64        // MAP output
	Report    *Report        // CRITIQUE output
}

// ExecuteFullSonar runs complete PING → ECHO → MAP → CRITIQUE cycle
func ExecuteFullSonar(ctx context.Context, sonar SonarEngine, app *AppState) (*SonarResult, error) {
	startTime := time.Now()

	// PING: Collect telemetry
	telemetry, err := sonar.Ping(ctx, app)
	if err != nil {
		return nil, err
	}

	// ECHO: Process metrics
	metrics, err := sonar.Echo(ctx, telemetry)
	if err != nil {
		return nil, err
	}

	// MAP: Normalize score
	score := sonar.Map(ctx, metrics)

	// CRITIQUE: Generate report
	report := sonar.Critique(ctx, score, metrics)
	report.Duration = time.Since(startTime)

	return &SonarResult{
		Telemetry: telemetry,
		Metrics:   metrics,
		Score:     score,
		Report:    report,
	}, nil
}

// BaseSonar provides common functionality for all sonar engines
type BaseSonar struct {
	name string
}

// NewBaseSonar creates a base sonar with given name
func NewBaseSonar(name string) *BaseSonar {
	return &BaseSonar{name: name}
}

// Name returns the sonar name
func (bs *BaseSonar) Name() string {
	return bs.name
}

// DetermineStatus converts score to status level
func DetermineStatus(score float64) StatusLevel {
	switch {
	case score >= 0.85:
		return StatusExcellent
	case score >= 0.70:
		return StatusOK
	case score >= 0.50:
		return StatusWarning
	default:
		return StatusCritical
	}
}

// ClampScore ensures score is in valid 0.0-1.0 range
func ClampScore(score float64) float64 {
	if score < 0.0 {
		return 0.0
	}
	if score > 1.0 {
		return 1.0
	}
	return score
}
