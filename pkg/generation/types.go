// Package generation implements D3-Enterprise Grade+ app generation with quality gates
//
// Production hardening layer that ensures generated apps meet Five Timbres standards
// Author: Colonel Sarah Mitchell (Site Reliability Engineering - Google SRE)
// Created: 2025-11-07
// Ported to Urban Lens: 2025-12-26
package generation

import "time"

// GeneratedApp represents a complete application ready for production
type GeneratedApp struct {
	Name        string
	RootPath    string
	Frontend    FrontendComponent
	Backend     BackendComponent
	Database    DatabaseComponent
	Tauri       TauriComponent
	Files       []GeneratedFile
	CreatedAt   time.Time
}

// FrontendComponent describes the frontend stack
type FrontendComponent struct {
	Framework string // "React", "Vue", "Svelte"
	Language  string // "TypeScript", "JavaScript"
	BuildTool string // "Vite", "Webpack", "Parcel"
	HasTests  bool
}

// BackendComponent describes the backend stack
type BackendComponent struct {
	Language  string // "Go", "Rust", "TypeScript"
	Framework string // "None", "Axum", "Express"
	HasTests  bool
}

// DatabaseComponent describes the database
type DatabaseComponent struct {
	Type         string // "SQLite", "PostgreSQL", "MySQL"
	HasSchema    bool
	HasMigration bool
}

// TauriComponent describes the desktop wrapper
type TauriComponent struct {
	Version string
	HasBuild bool
}

// GeneratedFile represents a single generated file
type GeneratedFile struct {
	Path    string
	Content string
	Size    int64
}

// Severity levels for quality issues
type Severity int

const (
	SeverityLow Severity = iota
	SeverityMedium
	SeverityHigh
	SeverityCritical
)

func (s Severity) String() string {
	switch s {
	case SeverityLow:
		return "LOW"
	case SeverityMedium:
		return "MEDIUM"
	case SeverityHigh:
		return "HIGH"
	case SeverityCritical:
		return "CRITICAL"
	default:
		return "UNKNOWN"
	}
}

// IssueType represents different types of completeness issues
type IssueType int

const (
	IssueTODO IssueType = iota
	IssueMock
	IssuePlaceholder
	IssueHardcoded
	IssueMissingTest
	IssueMissingError
)

func (it IssueType) String() string {
	switch it {
	case IssueTODO:
		return "TODO"
	case IssueMock:
		return "MOCK"
	case IssuePlaceholder:
		return "PLACEHOLDER"
	case IssueHardcoded:
		return "HARDCODED"
	case IssueMissingTest:
		return "MISSING_TEST"
	case IssueMissingError:
		return "MISSING_ERROR"
	default:
		return "UNKNOWN"
	}
}

// QualityMetrics represents Five Timbres measurement
type QualityMetrics struct {
	Correctness  float64 // Does it compile? Do tests pass?
	Performance  float64 // API latency, page load times
	Reliability  float64 // Error rates, crash frequency
	Synergy      float64 // Component integration, emergent gains
	Elegance     float64 // Code quality, maintainability
}

// QualityReport contains complete validation results
type QualityReport struct {
	// Five Timbres metrics
	Metrics QualityMetrics

	// Harmonic mean (all dimensions must be strong)
	HarmonicMean float64

	// Gate results
	BuildPassed    bool
	TestsPassed    bool
	PerformanceOK  bool
	SecurityOK     bool
	CompletenessOK bool

	// Detailed findings
	Failures        []QualityFailure
	Recommendations []string

	// Execution details
	Duration time.Duration
}

// QualityFailure describes a specific quality issue
type QualityFailure struct {
	Gate        string
	Severity    Severity
	Message     string
	File        string
	LineNumber  int
	AutoFixable bool
}

// ComponentBuildResult captures build outcome for a single component
type ComponentBuildResult struct {
	Success  bool
	Output   string
	Error    string
	Duration time.Duration
}

// TestFailure describes a specific test failure
type TestFailure struct {
	TestName string
	File     string
	Line     int
	Message  string
	Output   string
}

// CompletenessIssue represents a D3-Enterprise Grade+ violation
type CompletenessIssue struct {
	Type     IssueType
	File     string
	Line     int
	Severity Severity
	Message  string
}

// Vedic constants for quality thresholds
const (
	PHI                  = 0.618 // Golden ratio (minimum acceptable quality for each dimension)
	TargetHarmonicMean   = 0.95  // D3-Enterprise Grade+ target
	MaxAPILatencyP95     = 100   // milliseconds
	MaxPageLoadTime      = 2000  // milliseconds
	MaxDatabaseQueryTime = 50    // milliseconds
	MaxMemoryUsage       = 500   // megabytes
)
