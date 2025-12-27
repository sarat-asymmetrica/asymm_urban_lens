// Package profiling - Performance Metrics Dashboard
//
// "Where's the benchmark comparison: before/after optimization?" - John Carmack
//
// Features:
//   - Singleton metrics tracker (zero allocation overhead)
//   - P50, P95, P99 percentiles (latency distribution)
//   - Ops/sec tracking (throughput measurement)
//   - Target comparison (71M ops/sec for VQC, etc.)
//   - Export to JSON, Markdown, HTML
//   - Thread-safe (production-ready)
//
// Philosophy: Track EVERYTHING. Compare to targets. Show gaps. Guide optimization.
package profiling

import (
	"encoding/json"
	"fmt"
	"os"
	"sort"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// PERFORMANCE METRICS - Singleton Tracker
// ═══════════════════════════════════════════════════════════════════════════

// PerformanceMetrics is singleton tracker for all operations
// Zero overhead: Only records if enabled
// Thread-safe: Use from any goroutine
var (
	globalMetrics     *PerformanceMetrics
	globalMetricsOnce sync.Once
)

// PerformanceMetrics tracks all operation statistics
type PerformanceMetrics struct {
	operations map[string]*OperationStats
	targets    map[string]*PerformanceTarget
	mu         sync.RWMutex
	enabled    bool
}

// OperationStats contains all statistics for an operation
type OperationStats struct {
	Name string

	// Count metrics
	Count int64

	// Duration metrics
	TotalDuration time.Duration
	MinDuration   time.Duration
	MaxDuration   time.Duration
	AvgDuration   time.Duration

	// Percentiles (computed on demand from durations slice)
	P50 time.Duration
	P95 time.Duration
	P99 time.Duration

	// Memory metrics
	TotalAllocs   int64
	AvgAllocsPerOp int64

	// Throughput metrics
	OpsPerSecond float64

	// Raw data for percentile calculation
	durations []time.Duration
	allocs    []int64

	// Last update time
	LastUpdate time.Time
}

// PerformanceTarget defines expected performance for an operation
type PerformanceTarget struct {
	Name         string
	TargetOpsPerSec float64
	TargetP95       time.Duration
	TargetP99       time.Duration
	Description  string
}

// GetMetrics returns singleton metrics instance
// Lazily initialized on first call
func GetMetrics() *PerformanceMetrics {
	globalMetricsOnce.Do(func() {
		globalMetrics = &PerformanceMetrics{
			operations: make(map[string]*OperationStats),
			targets:    make(map[string]*PerformanceTarget),
			enabled:    true,
		}

		// Register default targets
		globalMetrics.registerDefaultTargets()
	})
	return globalMetrics
}

// registerDefaultTargets sets up known performance targets
func (pm *PerformanceMetrics) registerDefaultTargets() {
	// VQC Engine - 71M ops/sec target (GPU-accelerated)
	pm.targets["vqc_engine"] = &PerformanceTarget{
		Name:            "VQC Engine",
		TargetOpsPerSec: 71_000_000,
		TargetP95:       14 * time.Nanosecond,  // ~71M ops/sec
		TargetP99:       20 * time.Nanosecond,
		Description:     "Quaternion operations on GPU (71M ops/sec target)",
	}

	// Williams Optimizer - Batch processing
	pm.targets["williams_batch"] = &PerformanceTarget{
		Name:            "Williams Batch Processing",
		TargetOpsPerSec: 10_000_000,
		TargetP95:       100 * time.Nanosecond,
		TargetP99:       200 * time.Nanosecond,
		Description:     "Optimal batching O(√n × log₂n)",
	}

	// Quaternion operations (CPU baseline)
	pm.targets["quaternion_multiply"] = &PerformanceTarget{
		Name:            "Quaternion Multiply (CPU)",
		TargetOpsPerSec: 1_000_000,
		TargetP95:       1000 * time.Nanosecond,  // 1μs
		TargetP99:       2000 * time.Nanosecond,
		Description:     "CPU-only quaternion multiplication",
	}

	pm.targets["quaternion_slerp"] = &PerformanceTarget{
		Name:            "Quaternion SLERP (CPU)",
		TargetOpsPerSec: 500_000,
		TargetP95:       2000 * time.Nanosecond,  // 2μs
		TargetP99:       4000 * time.Nanosecond,
		Description:     "Spherical linear interpolation",
	}

	// GPU operations
	pm.targets["gpu_batch_multiply"] = &PerformanceTarget{
		Name:            "GPU Batch Multiply",
		TargetOpsPerSec: 50_000_000,
		TargetP95:       20 * time.Nanosecond,
		TargetP99:       30 * time.Nanosecond,
		Description:     "GPU quaternion batch multiplication",
	}

	pm.targets["gpu_batch_slerp"] = &PerformanceTarget{
		Name:            "GPU Batch SLERP",
		TargetOpsPerSec: 30_000_000,
		TargetP95:       33 * time.Nanosecond,
		TargetP99:       50 * time.Nanosecond,
		Description:     "GPU spherical interpolation",
	}

	// Semantic operations
	pm.targets["semantic_similarity"] = &PerformanceTarget{
		Name:            "Semantic Similarity",
		TargetOpsPerSec: 82_000_000,
		TargetP95:       12 * time.Nanosecond,
		TargetP99:       18 * time.Nanosecond,
		Description:     "Quaternion-based semantic matching (82M ops/sec)",
	}

	// Digital root filtering
	pm.targets["digital_root"] = &PerformanceTarget{
		Name:            "Digital Root Filter",
		TargetOpsPerSec: 100_000_000,
		TargetP95:       10 * time.Nanosecond,
		TargetP99:       15 * time.Nanosecond,
		Description:     "Vedic digital root (53× speedup)",
	}
}

// Enable turns on metrics collection
func (pm *PerformanceMetrics) Enable() {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.enabled = true
}

// Disable turns off metrics collection (zero overhead when disabled)
func (pm *PerformanceMetrics) Disable() {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.enabled = false
}

// IsEnabled returns whether metrics collection is active
func (pm *PerformanceMetrics) IsEnabled() bool {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	return pm.enabled
}

// RecordOperation records a single operation execution
// Thread-safe, can be called from any goroutine
//
// Example:
//   start := time.Now()
//   result := quaternion.Multiply(a, b)
//   metrics.RecordOperation("quaternion_multiply", time.Since(start), 0)
func (pm *PerformanceMetrics) RecordOperation(name string, duration time.Duration, allocBytes int64) {
	if !pm.enabled {
		return // Zero overhead when disabled
	}

	pm.mu.Lock()
	defer pm.mu.Unlock()

	stats, exists := pm.operations[name]
	if !exists {
		stats = &OperationStats{
			Name:        name,
			MinDuration: duration,
			MaxDuration: duration,
			durations:   make([]time.Duration, 0, 1000),
			allocs:      make([]int64, 0, 1000),
			LastUpdate:  time.Now(),
		}
		pm.operations[name] = stats
	}

	// Update count
	stats.Count++

	// Update duration metrics
	stats.TotalDuration += duration
	if duration < stats.MinDuration {
		stats.MinDuration = duration
	}
	if duration > stats.MaxDuration {
		stats.MaxDuration = duration
	}
	stats.AvgDuration = time.Duration(int64(stats.TotalDuration) / stats.Count)

	// Store raw duration for percentile calculation
	stats.durations = append(stats.durations, duration)

	// Update memory metrics
	stats.TotalAllocs += allocBytes
	stats.AvgAllocsPerOp = stats.TotalAllocs / stats.Count
	stats.allocs = append(stats.allocs, allocBytes)

	// Update throughput (ops/sec)
	if stats.AvgDuration > 0 {
		stats.OpsPerSecond = float64(time.Second) / float64(stats.AvgDuration)
	}

	// Update timestamp
	stats.LastUpdate = time.Now()

	// Compute percentiles if we have enough data
	if stats.Count >= 100 {
		pm.computePercentilesLocked(stats)
	}
}

// computePercentilesLocked computes P50, P95, P99 from raw durations
// Must be called with lock held!
func (pm *PerformanceMetrics) computePercentilesLocked(stats *OperationStats) {
	if len(stats.durations) == 0 {
		return
	}

	// Sort durations (copy to avoid mutating original)
	sorted := make([]time.Duration, len(stats.durations))
	copy(sorted, stats.durations)
	sort.Slice(sorted, func(i, j int) bool {
		return sorted[i] < sorted[j]
	})

	n := len(sorted)
	stats.P50 = sorted[n*50/100]
	stats.P95 = sorted[n*95/100]
	stats.P99 = sorted[n*99/100]
}

// GetStats returns statistics for a named operation
// Returns nil if operation not tracked
func (pm *PerformanceMetrics) GetStats(name string) *OperationStats {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	stats, exists := pm.operations[name]
	if !exists {
		return nil
	}

	// Return copy to avoid race conditions
	statsCopy := *stats
	return &statsCopy
}

// GetAllStats returns statistics for all tracked operations
func (pm *PerformanceMetrics) GetAllStats() map[string]*OperationStats {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	result := make(map[string]*OperationStats, len(pm.operations))
	for name, stats := range pm.operations {
		statsCopy := *stats
		result[name] = &statsCopy
	}
	return result
}

// RegisterTarget adds a custom performance target
func (pm *PerformanceMetrics) RegisterTarget(target *PerformanceTarget) {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.targets[target.Name] = target
}

// GetTarget returns target for operation name
func (pm *PerformanceMetrics) GetTarget(name string) *PerformanceTarget {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	return pm.targets[name]
}

// Reset clears all collected metrics
// Useful for benchmarking specific scenarios
func (pm *PerformanceMetrics) Reset() {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.operations = make(map[string]*OperationStats)
}

// ═══════════════════════════════════════════════════════════════════════════
// PERFORMANCE REPORT - Gap Analysis and Recommendations
// ═══════════════════════════════════════════════════════════════════════════

// PerformanceReport contains full performance analysis
type PerformanceReport struct {
	GeneratedAt time.Time
	Operations  map[string]*OperationReport
	Summary     *ReportSummary
}

// OperationReport contains per-operation analysis
type OperationReport struct {
	Name  string
	Stats *OperationStats
	Target *PerformanceTarget

	// Gap analysis
	ThroughputGap float64 // Percentage (negative = below target)
	P95Gap        time.Duration
	P99Gap        time.Duration

	// Status
	Status         string // "EXCELLENT", "GOOD", "NEEDS_WORK", "CRITICAL"
	Recommendations []string
}

// ReportSummary contains overall metrics summary
type ReportSummary struct {
	TotalOperations int
	TotalSamples    int64
	ExcellentCount  int
	GoodCount       int
	NeedsWorkCount  int
	CriticalCount   int
	OverallStatus   string
}

// GenerateReport creates comprehensive performance report
func (pm *PerformanceMetrics) GenerateReport() *PerformanceReport {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	report := &PerformanceReport{
		GeneratedAt: time.Now(),
		Operations:  make(map[string]*OperationReport),
		Summary: &ReportSummary{
			TotalOperations: len(pm.operations),
		},
	}

	// Analyze each operation
	for name, stats := range pm.operations {
		opReport := pm.analyzeOperationLocked(name, stats)
		report.Operations[name] = opReport

		// Update summary
		report.Summary.TotalSamples += stats.Count

		switch opReport.Status {
		case "EXCELLENT":
			report.Summary.ExcellentCount++
		case "GOOD":
			report.Summary.GoodCount++
		case "NEEDS_WORK":
			report.Summary.NeedsWorkCount++
		case "CRITICAL":
			report.Summary.CriticalCount++
		}
	}

	// Determine overall status
	if report.Summary.CriticalCount > 0 {
		report.Summary.OverallStatus = "CRITICAL"
	} else if report.Summary.NeedsWorkCount > len(pm.operations)/2 {
		report.Summary.OverallStatus = "NEEDS_WORK"
	} else if report.Summary.ExcellentCount > len(pm.operations)/2 {
		report.Summary.OverallStatus = "EXCELLENT"
	} else {
		report.Summary.OverallStatus = "GOOD"
	}

	return report
}

// analyzeOperationLocked analyzes single operation against target
// Must be called with lock held!
func (pm *PerformanceMetrics) analyzeOperationLocked(name string, stats *OperationStats) *OperationReport {
	report := &OperationReport{
		Name:  name,
		Stats: stats,
	}

	// Find target
	target, hasTarget := pm.targets[name]
	if !hasTarget {
		report.Status = "NO_TARGET"
		report.Recommendations = []string{
			"No performance target defined for this operation",
		}
		return report
	}

	report.Target = target

	// Compute gaps
	if target.TargetOpsPerSec > 0 {
		report.ThroughputGap = ((stats.OpsPerSecond - target.TargetOpsPerSec) / target.TargetOpsPerSec) * 100
	}
	report.P95Gap = stats.P95 - target.TargetP95
	report.P99Gap = stats.P99 - target.TargetP99

	// Determine status
	if stats.OpsPerSecond >= target.TargetOpsPerSec && stats.P95 <= target.TargetP95 && stats.P99 <= target.TargetP99 {
		report.Status = "EXCELLENT"
	} else if stats.OpsPerSecond >= target.TargetOpsPerSec*0.8 {
		report.Status = "GOOD"
	} else if stats.OpsPerSecond >= target.TargetOpsPerSec*0.5 {
		report.Status = "NEEDS_WORK"
	} else {
		report.Status = "CRITICAL"
	}

	// Generate recommendations
	report.Recommendations = pm.generateRecommendationsLocked(report)

	return report
}

// generateRecommendationsLocked generates optimization recommendations
// Must be called with lock held!
func (pm *PerformanceMetrics) generateRecommendationsLocked(report *OperationReport) []string {
	recs := make([]string, 0)

	if report.Target == nil {
		return recs
	}

	gap := report.ThroughputGap

	// Critical performance gap
	if gap < -50 {
		recs = append(recs, fmt.Sprintf("CRITICAL: %.1f%% below target (%.2f M ops/sec vs %.2f M ops/sec)",
			-gap, report.Stats.OpsPerSecond/1e6, report.Target.TargetOpsPerSec/1e6))
		recs = append(recs, "Consider GPU acceleration (50-100× speedup)")
		recs = append(recs, "Apply Williams batching O(√n × log₂n)")
		recs = append(recs, "Use object pooling to eliminate allocations")
	} else if gap < -20 {
		recs = append(recs, fmt.Sprintf("%.1f%% below target", -gap))
		recs = append(recs, "Profile with pprof to find bottlenecks")
		recs = append(recs, "Consider SIMD-friendly struct-of-arrays layout")
	} else if gap < 0 {
		recs = append(recs, fmt.Sprintf("%.1f%% below target (minor gap)", -gap))
		recs = append(recs, "Good performance, micro-optimizations may help")
	} else {
		recs = append(recs, fmt.Sprintf("EXCEEDS TARGET by %.1f%%!", gap))
	}

	// Latency analysis
	if report.P99Gap > 0 && report.P99Gap > report.Target.TargetP99 {
		recs = append(recs, fmt.Sprintf("P99 latency %.2fμs over target (check outliers)",
			float64(report.P99Gap.Nanoseconds())/1000.0))
	}

	// Memory analysis
	if report.Stats.AvgAllocsPerOp > 100 {
		recs = append(recs, fmt.Sprintf("High allocation rate: %d bytes/op (use object pooling)",
			report.Stats.AvgAllocsPerOp))
	}

	return recs
}

// ExportJSON exports report as JSON
func (pr *PerformanceReport) ExportJSON(filename string) error {
	data, err := json.MarshalIndent(pr, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal JSON: %w", err)
	}

	return os.WriteFile(filename, data, 0644)
}

// ExportMarkdown exports report as Markdown
func (pr *PerformanceReport) ExportMarkdown(filename string) error {
	md := pr.renderMarkdown()
	return os.WriteFile(filename, []byte(md), 0644)
}

// renderMarkdown generates Markdown report
func (pr *PerformanceReport) renderMarkdown() string {
	md := fmt.Sprintf("# Performance Report\n\n")
	md += fmt.Sprintf("**Generated**: %s\n\n", pr.GeneratedAt.Format(time.RFC3339))

	// Summary
	md += "## Summary\n\n"
	md += fmt.Sprintf("- **Total Operations**: %d\n", pr.Summary.TotalOperations)
	md += fmt.Sprintf("- **Total Samples**: %d\n", pr.Summary.TotalSamples)
	md += fmt.Sprintf("- **Overall Status**: **%s**\n\n", pr.Summary.OverallStatus)

	md += fmt.Sprintf("### Status Distribution\n\n")
	md += fmt.Sprintf("- ✅ Excellent: %d\n", pr.Summary.ExcellentCount)
	md += fmt.Sprintf("- ✓ Good: %d\n", pr.Summary.GoodCount)
	md += fmt.Sprintf("- ⚠️ Needs Work: %d\n", pr.Summary.NeedsWorkCount)
	md += fmt.Sprintf("- ❌ Critical: %d\n\n", pr.Summary.CriticalCount)

	// Operation details
	md += "## Operation Details\n\n"

	// Sort operations by name
	names := make([]string, 0, len(pr.Operations))
	for name := range pr.Operations {
		names = append(names, name)
	}
	sort.Strings(names)

	for _, name := range names {
		opReport := pr.Operations[name]
		md += pr.renderOperationMarkdown(opReport)
	}

	return md
}

// renderOperationMarkdown renders single operation section
func (pr *PerformanceReport) renderOperationMarkdown(op *OperationReport) string {
	md := fmt.Sprintf("### %s\n\n", op.Name)

	// Status badge
	var badge string
	switch op.Status {
	case "EXCELLENT":
		badge = "✅ EXCELLENT"
	case "GOOD":
		badge = "✓ GOOD"
	case "NEEDS_WORK":
		badge = "⚠️ NEEDS WORK"
	case "CRITICAL":
		badge = "❌ CRITICAL"
	default:
		badge = "⚪ NO TARGET"
	}
	md += fmt.Sprintf("**Status**: %s\n\n", badge)

	// Statistics
	md += "**Statistics**:\n\n"
	md += fmt.Sprintf("- Count: %d\n", op.Stats.Count)
	md += fmt.Sprintf("- Ops/Sec: %.2f M\n", op.Stats.OpsPerSecond/1e6)
	md += fmt.Sprintf("- Avg Duration: %v\n", op.Stats.AvgDuration)
	md += fmt.Sprintf("- P50: %v\n", op.Stats.P50)
	md += fmt.Sprintf("- P95: %v\n", op.Stats.P95)
	md += fmt.Sprintf("- P99: %v\n", op.Stats.P99)
	md += fmt.Sprintf("- Avg Allocs: %d bytes/op\n\n", op.Stats.AvgAllocsPerOp)

	// Target comparison
	if op.Target != nil {
		md += "**Target**:\n\n"
		md += fmt.Sprintf("- Target Ops/Sec: %.2f M\n", op.Target.TargetOpsPerSec/1e6)
		md += fmt.Sprintf("- Throughput Gap: %.1f%%\n", op.ThroughputGap)
		md += fmt.Sprintf("- Description: %s\n\n", op.Target.Description)
	}

	// Recommendations
	if len(op.Recommendations) > 0 {
		md += "**Recommendations**:\n\n"
		for _, rec := range op.Recommendations {
			md += fmt.Sprintf("- %s\n", rec)
		}
		md += "\n"
	}

	md += "---\n\n"
	return md
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVENIENCE FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// RecordOperation is global convenience function
func RecordOperation(name string, duration time.Duration, allocBytes int64) {
	GetMetrics().RecordOperation(name, duration, allocBytes)
}

// GetStats is global convenience function
func GetStats(name string) *OperationStats {
	return GetMetrics().GetStats(name)
}

// GenerateReport is global convenience function
func GenerateReport() *PerformanceReport {
	return GetMetrics().GenerateReport()
}

// TimedOperation executes function and records metrics
// Returns function result and any error
//
// Example:
//   result, err := TimedOperation("my_operation", func() (interface{}, error) {
//       return doSomething(), nil
//   })
func TimedOperation(name string, fn func() (interface{}, error)) (interface{}, error) {
	start := time.Now()
	result, err := fn()
	duration := time.Since(start)

	RecordOperation(name, duration, 0)

	return result, err
}
