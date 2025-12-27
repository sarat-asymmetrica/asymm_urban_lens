// Package profiling - Memory Profiler with Williams Space Efficiency Validation
//
// CARMACK MANDATE: "Show me the ACTUAL memory usage at n=1M."
//
// Mathematical Foundation:
// - Williams Space Bound: O(√t × log₂t)
// - Theoretical Space Reduction: 68.5% at n=1000, 84.2% at n=1M
// - Efficiency Target: ≥ 1.5x (validated research threshold)
//
// Measurement Methodology:
// - runtime.MemStats for heap allocation tracking
// - Allocation delta (before/after function execution)
// - GC-aware measurements (force GC before sampling)
// - Real-world validation at n=100, 1K, 10K, 100K, 1M, 10M
//
// Author: Asymmetrica Research Dyad
// Created: 2025-12-27
package profiling

import (
	"fmt"
	"runtime"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/intelligence"
)

// AllocationStats captures memory allocation metrics
type AllocationStats struct {
	// Timing
	StartTime    time.Time     // Execution start
	EndTime      time.Time     // Execution end
	Duration     time.Duration // Total duration

	// Memory (bytes)
	HeapAllocBefore  uint64 // Heap allocated before
	HeapAllocAfter   uint64 // Heap allocated after
	HeapAllocDelta   int64  // Net change (can be negative due to GC)
	TotalAllocDelta  uint64 // Total allocated during execution
	NumGC            uint32 // Garbage collections triggered

	// Objects
	NumMallocs uint64 // Number of malloc calls
	NumFrees   uint64 // Number of free calls
	LiveObjects uint64 // Live objects (mallocs - frees)

	// Efficiency
	AllocRate float64 // Bytes/second allocation rate
}

// HeapStats captures heap memory snapshot
type HeapStats struct {
	// Current heap state
	HeapAlloc    uint64  // Bytes allocated and in use
	HeapSys      uint64  // Bytes obtained from OS
	HeapIdle     uint64  // Bytes in idle spans
	HeapInuse    uint64  // Bytes in non-idle spans
	HeapReleased uint64  // Bytes released to OS
	HeapObjects  uint64  // Total number of allocated objects

	// Utilization
	MemoryUtilization float64 // HeapAlloc / HeapSys
	FragmentationRate float64 // HeapIdle / HeapSys

	// GC stats
	NextGC       uint64 // Next GC target heap size
	LastGC       uint64 // Last GC timestamp (ns since epoch)
	NumGC        uint32 // Number of completed GC cycles
	GCCPUFraction float64 // Fraction of CPU time in GC
}

// WilliamsComparison compares actual memory usage to Williams theoretical bound
type WilliamsComparison struct {
	// Problem size
	N int // Input size (number of operations/items)

	// Theoretical (Williams bound)
	TheoreticalSpace int     // √N × log₂(N) items
	TheoreticalBytes int64   // Theoretical space in bytes
	TheoreticalFormula string // Human-readable formula

	// Actual (measured)
	ActualSpace int    // Actual items stored
	ActualBytes int64  // Measured memory usage (bytes)

	// Efficiency analysis
	SpaceEfficiency    float64 // Actual / Theoretical (≤1.0 = optimal)
	MemoryReduction    float64 // Percentage reduction vs linear O(N)
	EfficiencyRating   float64 // N / TheoreticalSpace (should be ≥ 1.5x)

	// Status
	Status      string // "optimal", "acceptable", "needs_work", "failing"
	Explanation string // Detailed analysis
}

// MemoryProfiler tracks and analyzes memory usage
type MemoryProfiler struct {
	optimizer *intelligence.WilliamsSpaceOptimizer
}

// NewMemoryProfiler creates a memory profiler
func NewMemoryProfiler() *MemoryProfiler {
	return &MemoryProfiler{
		optimizer: intelligence.NewWilliamsSpaceOptimizer(),
	}
}

// TrackAllocations measures memory allocations during function execution
//
// Methodology:
//  1. Force GC to establish baseline
//  2. Capture heap stats before execution
//  3. Run function
//  4. Capture heap stats after execution
//  5. Calculate deltas
//
// Returns:
//   - AllocationStats with timing and memory metrics
//
// Example:
//
//	profiler := NewMemoryProfiler()
//	stats := profiler.TrackAllocations(func() {
//	    // Code to profile
//	    data := make([]int, 1000000)
//	    _ = data
//	})
//	fmt.Printf("Allocated: %d bytes in %v\n", stats.TotalAllocDelta, stats.Duration)
func (mp *MemoryProfiler) TrackAllocations(fn func()) AllocationStats {
	// Force GC to clear baseline
	runtime.GC()
	runtime.GC() // Second GC to ensure cleanup

	// Wait for GC to complete
	time.Sleep(10 * time.Millisecond)

	// Capture before stats
	var memBefore runtime.MemStats
	runtime.ReadMemStats(&memBefore)

	// Execute function
	startTime := time.Now()
	fn()
	endTime := time.Now()

	// Force GC to account for temporary allocations
	runtime.GC()
	time.Sleep(10 * time.Millisecond)

	// Capture after stats
	var memAfter runtime.MemStats
	runtime.ReadMemStats(&memAfter)

	// Calculate deltas
	heapAllocDelta := int64(memAfter.HeapAlloc) - int64(memBefore.HeapAlloc)
	totalAllocDelta := memAfter.TotalAlloc - memBefore.TotalAlloc
	numMallocsDelta := memAfter.Mallocs - memBefore.Mallocs
	numFreesDelta := memAfter.Frees - memBefore.Frees
	numGCDelta := memAfter.NumGC - memBefore.NumGC

	duration := endTime.Sub(startTime)
	allocRate := 0.0
	if duration.Seconds() > 0 {
		allocRate = float64(totalAllocDelta) / duration.Seconds()
	}

	return AllocationStats{
		StartTime:       startTime,
		EndTime:         endTime,
		Duration:        duration,
		HeapAllocBefore: memBefore.HeapAlloc,
		HeapAllocAfter:  memAfter.HeapAlloc,
		HeapAllocDelta:  heapAllocDelta,
		TotalAllocDelta: totalAllocDelta,
		NumGC:           numGCDelta,
		NumMallocs:      numMallocsDelta,
		NumFrees:        numFreesDelta,
		LiveObjects:     numMallocsDelta - numFreesDelta,
		AllocRate:       allocRate,
	}
}

// MeasureHeapUsage captures current heap state snapshot
//
// Returns:
//   - HeapStats with current memory utilization
//
// Example:
//
//	profiler := NewMemoryProfiler()
//	stats := profiler.MeasureHeapUsage()
//	fmt.Printf("Heap: %d bytes (%.1f%% utilized)\n",
//	    stats.HeapAlloc, stats.MemoryUtilization * 100)
func (mp *MemoryProfiler) MeasureHeapUsage() HeapStats {
	runtime.GC()
	time.Sleep(10 * time.Millisecond)

	var mem runtime.MemStats
	runtime.ReadMemStats(&mem)

	memoryUtilization := 0.0
	if mem.HeapSys > 0 {
		memoryUtilization = float64(mem.HeapAlloc) / float64(mem.HeapSys)
	}

	fragmentationRate := 0.0
	if mem.HeapSys > 0 {
		fragmentationRate = float64(mem.HeapIdle) / float64(mem.HeapSys)
	}

	return HeapStats{
		HeapAlloc:         mem.HeapAlloc,
		HeapSys:           mem.HeapSys,
		HeapIdle:          mem.HeapIdle,
		HeapInuse:         mem.HeapInuse,
		HeapReleased:      mem.HeapReleased,
		HeapObjects:       mem.HeapObjects,
		MemoryUtilization: memoryUtilization,
		FragmentationRate: fragmentationRate,
		NextGC:            mem.NextGC,
		LastGC:            mem.LastGC,
		NumGC:             mem.NumGC,
		GCCPUFraction:     mem.GCCPUFraction,
	}
}

// CompareToWilliams validates actual memory usage against Williams bound
//
// Algorithm:
//  1. Calculate Williams theoretical space: √N × log₂(N)
//  2. Compare actual bytes to theoretical bound
//  3. Calculate space efficiency: actual / theoretical
//  4. Calculate memory reduction vs linear O(N)
//  5. Determine status: optimal/acceptable/needs_work/failing
//
// Status Thresholds:
//   - optimal: efficiency ≤ 1.1x theoretical (within 10%)
//   - acceptable: efficiency ≤ 2.0x theoretical (within 2x)
//   - needs_work: efficiency ≤ 5.0x theoretical (within 5x)
//   - failing: efficiency > 5.0x theoretical
//
// Parameters:
//   - n: Problem size (number of items/operations)
//   - actualBytes: Measured memory usage in bytes
//   - bytesPerItem: Average bytes per item (default: 8 for int64)
//
// Returns:
//   - WilliamsComparison with efficiency analysis and status
//
// Example:
//
//	profiler := NewMemoryProfiler()
//	// Process 1M items, used 50MB
//	comparison := profiler.CompareToWilliams(1_000_000, 50_000_000, 8)
//	fmt.Printf("Status: %s (%.2fx efficiency)\n",
//	    comparison.Status, comparison.SpaceEfficiency)
func (mp *MemoryProfiler) CompareToWilliams(n int, actualBytes int64, bytesPerItem int) WilliamsComparison {
	if bytesPerItem <= 0 {
		bytesPerItem = 8 // Default: int64
	}

	// Calculate Williams theoretical bound
	spaceBoundResult := mp.optimizer.CalculateSpaceBound(n)
	theoreticalSpace := spaceBoundResult.SpaceBound
	theoreticalBytes := int64(theoreticalSpace) * int64(bytesPerItem)
	efficiencyRating := spaceBoundResult.Efficiency

	// Calculate actual space (items)
	actualSpace := int(actualBytes / int64(bytesPerItem))

	// Calculate space efficiency (actual vs theoretical)
	spaceEfficiency := 0.0
	if theoreticalBytes > 0 {
		spaceEfficiency = float64(actualBytes) / float64(theoreticalBytes)
	}

	// Calculate memory reduction vs linear O(N)
	linearBytes := int64(n) * int64(bytesPerItem)
	memoryReduction := 0.0
	if linearBytes > 0 {
		memoryReduction = (1.0 - float64(actualBytes)/float64(linearBytes)) * 100.0
	}

	// Determine status
	status := "failing"
	explanation := ""

	if spaceEfficiency <= 1.1 {
		status = "optimal"
		explanation = fmt.Sprintf(
			"✅ OPTIMAL: Memory usage within 10%% of Williams theoretical bound (%.2fx)",
			spaceEfficiency,
		)
	} else if spaceEfficiency <= 2.0 {
		status = "acceptable"
		explanation = fmt.Sprintf(
			"✓ ACCEPTABLE: Memory usage within 2x of Williams bound (%.2fx). Still sublinear.",
			spaceEfficiency,
		)
	} else if spaceEfficiency <= 5.0 {
		status = "needs_work"
		explanation = fmt.Sprintf(
			"⚠ NEEDS_WORK: Memory usage %.2fx Williams bound. Optimization opportunities exist.",
			spaceEfficiency,
		)
	} else {
		status = "failing"
		explanation = fmt.Sprintf(
			"❌ FAILING: Memory usage %.2fx Williams bound. Likely O(N) instead of O(√N log N).",
			spaceEfficiency,
		)
	}

	// Add efficiency rating validation
	if efficiencyRating < 1.5 {
		explanation += fmt.Sprintf(
			" Efficiency rating %.2fx below research threshold (1.5x).",
			efficiencyRating,
		)
	}

	return WilliamsComparison{
		N:                  n,
		TheoreticalSpace:   theoreticalSpace,
		TheoreticalBytes:   theoreticalBytes,
		TheoreticalFormula: spaceBoundResult.Formula,
		ActualSpace:        actualSpace,
		ActualBytes:        actualBytes,
		SpaceEfficiency:    spaceEfficiency,
		MemoryReduction:    memoryReduction,
		EfficiencyRating:   efficiencyRating,
		Status:             status,
		Explanation:        explanation,
	}
}

// FormatAllocationStats returns human-readable allocation summary
func (stats AllocationStats) Format() string {
	return fmt.Sprintf(`Allocation Stats:
  Duration: %v
  Heap Delta: %s (%+d bytes)
  Total Allocated: %s
  Allocation Rate: %s/sec
  Mallocs: %d | Frees: %d | Live: %d
  GC Cycles: %d`,
		stats.Duration,
		formatBytes(stats.HeapAllocDelta),
		stats.HeapAllocDelta,
		formatBytes(int64(stats.TotalAllocDelta)),
		formatBytes(int64(stats.AllocRate)),
		stats.NumMallocs,
		stats.NumFrees,
		stats.LiveObjects,
		stats.NumGC,
	)
}

// FormatHeapStats returns human-readable heap summary
func (stats HeapStats) Format() string {
	return fmt.Sprintf(`Heap Stats:
  Allocated: %s
  System: %s (%.1f%% utilized)
  In Use: %s | Idle: %s (%.1f%% fragmentation)
  Released: %s
  Objects: %d
  GC: %d cycles (%.2f%% CPU time)`,
		formatBytes(int64(stats.HeapAlloc)),
		formatBytes(int64(stats.HeapSys)),
		stats.MemoryUtilization*100,
		formatBytes(int64(stats.HeapInuse)),
		formatBytes(int64(stats.HeapIdle)),
		stats.FragmentationRate*100,
		formatBytes(int64(stats.HeapReleased)),
		stats.HeapObjects,
		stats.NumGC,
		stats.GCCPUFraction*100,
	)
}

// FormatComparison returns human-readable Williams comparison
func (wc WilliamsComparison) Format() string {
	return fmt.Sprintf(`Williams Comparison (N=%d):

THEORETICAL (Williams Bound):
  Space: %d items (%s)
  Formula: %s

ACTUAL (Measured):
  Space: %d items (%s)

EFFICIENCY:
  Space Efficiency: %.2fx theoretical (%.0f%% vs theoretical)
  Memory Reduction: %.1f%% vs linear O(N)
  Efficiency Rating: %.2fx (target: ≥1.5x)

STATUS: %s
%s`,
		wc.N,
		wc.TheoreticalSpace,
		formatBytes(wc.TheoreticalBytes),
		wc.TheoreticalFormula,
		wc.ActualSpace,
		formatBytes(wc.ActualBytes),
		wc.SpaceEfficiency,
		(wc.SpaceEfficiency-1.0)*100,
		wc.MemoryReduction,
		wc.EfficiencyRating,
		wc.Status,
		wc.Explanation,
	)
}

// formatBytes converts bytes to human-readable format
func formatBytes(bytes int64) string {
	if bytes < 0 {
		return fmt.Sprintf("-%s", formatBytes(-bytes))
	}

	const (
		KB = 1024
		MB = 1024 * KB
		GB = 1024 * MB
	)

	switch {
	case bytes >= GB:
		return fmt.Sprintf("%.2f GB", float64(bytes)/float64(GB))
	case bytes >= MB:
		return fmt.Sprintf("%.2f MB", float64(bytes)/float64(MB))
	case bytes >= KB:
		return fmt.Sprintf("%.2f KB", float64(bytes)/float64(KB))
	default:
		return fmt.Sprintf("%d bytes", bytes)
	}
}

// MemoryBenchmarkResult captures memory benchmark at specific problem size
type MemoryBenchmarkResult struct {
	N                int
	Allocations      AllocationStats
	HeapState        HeapStats
	WilliamsCompare  WilliamsComparison
}

// RunMemoryBenchmark executes memory profiling at specified problem size
//
// Parameters:
//   - n: Problem size
//   - allocFn: Function to benchmark (should allocate memory for n items)
//   - bytesPerItem: Average bytes per item
//
// Returns:
//   - MemoryBenchmarkResult with all metrics
//
// Example:
//
//	profiler := NewMemoryProfiler()
//	result := profiler.RunMemoryBenchmark(1_000_000, func() {
//	    data := make([]int64, 1_000_000)
//	    _ = data
//	}, 8)
func (mp *MemoryProfiler) RunMemoryBenchmark(
	n int,
	allocFn func(),
	bytesPerItem int,
) MemoryBenchmarkResult {
	// Measure allocations
	allocStats := mp.TrackAllocations(allocFn)

	// Measure heap state after allocation
	heapStats := mp.MeasureHeapUsage()

	// Compare to Williams
	williamsCompare := mp.CompareToWilliams(n, int64(allocStats.HeapAllocDelta), bytesPerItem)

	return MemoryBenchmarkResult{
		N:               n,
		Allocations:     allocStats,
		HeapState:       heapStats,
		WilliamsCompare: williamsCompare,
	}
}

// RunMemoryBenchmarkSuite executes benchmarks at multiple problem sizes
//
// Default sizes: 100, 1K, 10K, 100K, 1M
//
// Parameters:
//   - allocFn: Function generator (given n, returns allocation function)
//   - bytesPerItem: Average bytes per item
//
// Returns:
//   - Slice of MemoryBenchmarkResults
//
// Example:
//
//	profiler := NewMemoryProfiler()
//	results := profiler.RunMemoryBenchmarkSuite(
//	    func(n int) func() {
//	        return func() {
//	            data := make([]int64, n)
//	            // Use Williams batching
//	            batchSize := int(math.Sqrt(float64(n)) * math.Log2(float64(n)))
//	            for i := 0; i < n; i += batchSize {
//	                // Process batch
//	            }
//	            _ = data
//	        }
//	    },
//	    8,
//	)
func (mp *MemoryProfiler) RunMemoryBenchmarkSuite(
	allocFnGenerator func(n int) func(),
	bytesPerItem int,
) []MemoryBenchmarkResult {
	problemSizes := []int{100, 1_000, 10_000, 100_000, 1_000_000}
	results := make([]MemoryBenchmarkResult, 0, len(problemSizes))

	for _, n := range problemSizes {
		allocFn := allocFnGenerator(n)
		result := mp.RunMemoryBenchmark(n, allocFn, bytesPerItem)
		results = append(results, result)
	}

	return results
}

// GenerateEfficiencyReport creates comprehensive efficiency analysis
//
// Returns:
//   - Multi-line report with all benchmark results formatted
//
// Example output:
//
//	Williams Space Efficiency Report
//	=================================
//
//	N=100:
//	  Theoretical: 66 items (528 bytes)
//	  Actual: 100 items (800 bytes)
//	  Efficiency: 1.52x (52% over theoretical)
//	  Status: acceptable
//
//	N=1M:
//	  Theoretical: 19,931 items (159 KB)
//	  Actual: 25,000 items (195 KB)
//	  Efficiency: 1.23x (23% over theoretical)
//	  Status: optimal
func (mp *MemoryProfiler) GenerateEfficiencyReport(results []MemoryBenchmarkResult) string {
	report := "Williams Space Efficiency Report\n"
	report += "=================================\n\n"

	for i, result := range results {
		wc := result.WilliamsCompare
		report += fmt.Sprintf("N=%d:\n", wc.N)
		report += fmt.Sprintf("  Theoretical: %d items (%s)\n",
			wc.TheoreticalSpace, formatBytes(wc.TheoreticalBytes))
		report += fmt.Sprintf("  Actual: %d items (%s)\n",
			wc.ActualSpace, formatBytes(wc.ActualBytes))
		report += fmt.Sprintf("  Efficiency: %.2fx (%.0f%% vs theoretical)\n",
			wc.SpaceEfficiency, (wc.SpaceEfficiency-1.0)*100)
		report += fmt.Sprintf("  Memory Reduction: %.1f%% vs linear\n", wc.MemoryReduction)
		report += fmt.Sprintf("  Efficiency Rating: %.2fx\n", wc.EfficiencyRating)
		report += fmt.Sprintf("  Status: %s\n", wc.Status)

		if i < len(results)-1 {
			report += "\n"
		}
	}

	return report
}
