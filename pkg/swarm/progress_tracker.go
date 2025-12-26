// Package swarm - Progress Tracker
//
// Visualizes healing progress and generates human-readable reports
// Author: Agent 3.3 (Dr. Priya Sharma - Mathematical Convergence Theory, Cambridge)
// Created: 2025-11-07
//
// Provides real-time progress visibility with terminal formatting
package swarm

import (
	"fmt"
	"strings"
	"time"
)

// ProgressTracker provides progress visibility
type ProgressTracker struct {
	monitor *ConvergenceMonitor
}

// NewProgressTracker creates tracker for given monitor
func NewProgressTracker(monitor *ConvergenceMonitor) *ProgressTracker {
	return &ProgressTracker{
		monitor: monitor,
	}
}

// GetProgressReport generates comprehensive progress report
func (pt *ProgressTracker) GetProgressReport() ProgressReport {
	if len(pt.monitor.history) == 0 {
		return ProgressReport{
			StartErrors:     pt.monitor.startErrors,
			CurrentErrors:   pt.monitor.startErrors,
			ErrorsFixed:     0,
			ProgressPercent: 0.0,
			IterationCount:  0,
			Status:          "Initializing",
			TimeElapsed:     time.Since(pt.monitor.startTime),
			FixHistory:      []FixHistoryEntry{},
		}
	}

	latest := pt.monitor.history[len(pt.monitor.history)-1]
	errorsFixed := pt.monitor.startErrors - latest.ErrorCount
	progressPercent := 0.0
	if pt.monitor.startErrors > 0 {
		progressPercent = (float64(errorsFixed) / float64(pt.monitor.startErrors)) * 100.0
	}

	// Calculate estimated time remaining
	remaining := pt.estimateTimeRemaining()

	// Build fix history
	fixHistory := pt.buildFixHistory()

	// Get current status
	convergenceStatus := pt.monitor.CheckConvergence()

	return ProgressReport{
		StartErrors:        pt.monitor.startErrors,
		CurrentErrors:      latest.ErrorCount,
		ErrorsFixed:        errorsFixed,
		ProgressPercent:    progressPercent,
		IterationCount:     len(pt.monitor.history),
		Status:             string(convergenceStatus.Status),
		TimeElapsed:        time.Since(pt.monitor.startTime),
		EstimatedRemaining: remaining,
		FixHistory:         fixHistory,
		ProgressRate:       latest.ProgressRate,
		ConvergenceVelocity: latest.ConvergenceVelocity,
	}
}

// ProgressReport summarizes healing progress
type ProgressReport struct {
	StartErrors         int               // Initial error count
	CurrentErrors       int               // Current error count
	ErrorsFixed         int               // Total errors fixed
	ProgressPercent     float64           // Percentage complete (0-100)
	IterationCount      int               // Iterations completed
	Status              string            // Current status (converging, stuck, etc.)
	TimeElapsed         time.Duration     // Total time elapsed
	EstimatedRemaining  time.Duration     // Estimated time to completion
	FixHistory          []FixHistoryEntry // History of successful fixes
	ProgressRate        float64           // Errors per iteration
	ConvergenceVelocity float64           // Errors per second
}

// FixHistoryEntry records one successful fix
type FixHistoryEntry struct {
	Iteration   int       // When fix was applied
	ErrorFixed  string    // Error that was fixed
	VariantUsed string    // Variant ID used
	Confidence  float64   // Variant confidence
	ErrorDelta  int       // Errors reduced this iteration
	Timestamp   time.Time // When fix was applied
}

// FormatProgress returns colored terminal output
func (pt *ProgressTracker) FormatProgress() string {
	report := pt.GetProgressReport()

	var sb strings.Builder

	// Header
	sb.WriteString("\n")
	sb.WriteString("╔══════════════════════════════════════════════════════════════╗\n")
	sb.WriteString("║              ANANTA SWARM HEALING PROGRESS                   ║\n")
	sb.WriteString("╚══════════════════════════════════════════════════════════════╝\n")
	sb.WriteString("\n")

	// Progress bar
	progressBar := renderProgressBar(report.ProgressPercent, 50)
	sb.WriteString(fmt.Sprintf("Progress: %s %.1f%%\n", progressBar, report.ProgressPercent))
	sb.WriteString(fmt.Sprintf("Errors:   %d → %d (-%d fixed)\n",
		report.StartErrors,
		report.CurrentErrors,
		report.ErrorsFixed))
	sb.WriteString("\n")

	// Iteration info
	sb.WriteString(fmt.Sprintf("Iteration:  %d\n", report.IterationCount))
	sb.WriteString(fmt.Sprintf("Rate:       %.2f errors/iteration\n", report.ProgressRate))
	sb.WriteString(fmt.Sprintf("Velocity:   %.2f errors/second\n", report.ConvergenceVelocity))
	sb.WriteString(fmt.Sprintf("Status:     %s\n", formatStatus(report.Status)))
	sb.WriteString("\n")

	// Time info
	sb.WriteString(fmt.Sprintf("Elapsed:    %s\n", formatDuration(report.TimeElapsed)))
	if report.EstimatedRemaining > 0 {
		sb.WriteString(fmt.Sprintf("Remaining:  ~%s\n", formatDuration(report.EstimatedRemaining)))
	} else if report.EstimatedRemaining == -1 {
		sb.WriteString("Remaining:  Unknown (insufficient data)\n")
	}
	sb.WriteString("\n")

	// Recent fixes (last 5)
	if len(report.FixHistory) > 0 {
		sb.WriteString("Recent Fixes:\n")
		start := 0
		if len(report.FixHistory) > 5 {
			start = len(report.FixHistory) - 5
		}
		for i := start; i < len(report.FixHistory); i++ {
			fix := report.FixHistory[i]
			sb.WriteString(fmt.Sprintf("  [%d] %s (δ=%d)\n",
				fix.Iteration,
				fix.ErrorFixed,
				fix.ErrorDelta))
		}
	}

	sb.WriteString("\n")

	return sb.String()
}

// FormatCompact returns single-line progress summary
func (pt *ProgressTracker) FormatCompact() string {
	report := pt.GetProgressReport()
	bar := renderProgressBar(report.ProgressPercent, 20)
	return fmt.Sprintf("[%s] %d/%d errors | Iter %d | %.1f%% | %s",
		bar,
		report.ErrorsFixed,
		report.StartErrors,
		report.IterationCount,
		report.ProgressPercent,
		report.Status)
}

// estimateTimeRemaining calculates ETA based on current velocity
func (pt *ProgressTracker) estimateTimeRemaining() time.Duration {
	if len(pt.monitor.history) == 0 {
		return -1 // Unknown
	}

	latest := pt.monitor.history[len(pt.monitor.history)-1]
	if latest.ErrorCount == 0 {
		return 0 // Done
	}

	if latest.ConvergenceVelocity <= 0 {
		return -1 // No progress - infinite time
	}

	// Use recent average velocity for estimate
	velocities := make([]float64, 0, 5)
	start := len(pt.monitor.history) - 5
	if start < 0 {
		start = 0
	}
	for i := start; i < len(pt.monitor.history); i++ {
		if pt.monitor.history[i].ConvergenceVelocity > 0 {
			velocities = append(velocities, pt.monitor.history[i].ConvergenceVelocity)
		}
	}

	if len(velocities) == 0 {
		return -1
	}

	avgVelocity := harmonicMean(velocities)
	if avgVelocity <= 0 {
		return -1
	}

	secondsRemaining := float64(latest.ErrorCount) / avgVelocity
	return time.Duration(secondsRemaining * float64(time.Second))
}

// buildFixHistory extracts successful fixes from iteration history
func (pt *ProgressTracker) buildFixHistory() []FixHistoryEntry {
	history := make([]FixHistoryEntry, 0, len(pt.monitor.history))

	for _, state := range pt.monitor.history {
		if state.BestVariant != nil && state.BestVariant.Success {
			entry := FixHistoryEntry{
				Iteration:  state.Iteration,
				ErrorFixed: extractFirstError(state.BestVariant.CompilerOutput),
				VariantUsed: fmt.Sprintf("%d", state.BestVariant.VariantID), // Convert int to string
				Confidence: state.BestVariant.Confidence,
				ErrorDelta: state.BestVariant.ErrorDelta,
				Timestamp:  state.BestVariant.AppliedAt,
			}
			history = append(history, entry)
		}
	}

	return history
}

// renderProgressBar creates ASCII progress bar
func renderProgressBar(percent float64, width int) string {
	if percent < 0 {
		percent = 0
	}
	if percent > 100 {
		percent = 100
	}

	filled := int((percent / 100.0) * float64(width))
	empty := width - filled

	bar := strings.Repeat("█", filled) + strings.Repeat("░", empty)
	return bar
}

// formatStatus adds color/emoji to status
func formatStatus(status string) string {
	switch status {
	case "converging":
		return "✓ Converging"
	case "complete":
		return "✓ Complete!"
	case "stuck":
		return "✗ Stuck"
	case "oscillating":
		return "⟳ Oscillating"
	case "regressing":
		return "⚠ Regressing"
	case "max_iterations":
		return "⚠ Max Iterations"
	default:
		return "? " + status
	}
}

// formatDuration formats duration in human-readable format
func formatDuration(d time.Duration) string {
	if d < 0 {
		return "unknown"
	}
	if d < time.Second {
		return fmt.Sprintf("%dms", d.Milliseconds())
	}
	if d < time.Minute {
		return fmt.Sprintf("%.1fs", d.Seconds())
	}
	if d < time.Hour {
		mins := int(d.Minutes())
		secs := int(d.Seconds()) % 60
		return fmt.Sprintf("%dm%ds", mins, secs)
	}
	hours := int(d.Hours())
	mins := int(d.Minutes()) % 60
	return fmt.Sprintf("%dh%dm", hours, mins)
}

// extractFirstError extracts first error message from compiler output
// Simplified - production would use full parser
func extractFirstError(compilerOutput string) string {
	lines := strings.Split(compilerOutput, "\n")
	for _, line := range lines {
		if strings.Contains(line, "error:") {
			// Extract error message (simplified)
			if len(line) > 50 {
				return line[:50] + "..."
			}
			return line
		}
	}
	return "Unknown error"
}
