// Package profiling - Comprehensive pprof infrastructure for Asymmetrica UrbanLens
//
// "Performance claims without profiler evidence are fiction." - John Carmack
//
// Features:
//   - Easy pprof wrapper (CPU, memory, trace, goroutine, block, mutex)
//   - BenchmarkSuite for coordinated benchmarking
//   - Williams-optimized batch processing
//   - GPU/VQC integration metrics
//   - Automated report generation
//
// Philosophy: Measure EVERYTHING. No guessing. Math > Claims.
package profiling

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"runtime/trace"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// PROFILER - Easy pprof wrapper with CPU, Memory, Trace support
// ═══════════════════════════════════════════════════════════════════════════

// Profiler manages all profiling operations
type Profiler struct {
	outputDir      string
	cpuProfileFile *os.File
	traceFile      *os.File
	mu             sync.Mutex
}

// NewProfiler creates profiler with output directory
// Directory is created if it doesn't exist
func NewProfiler(outputDir string) (*Profiler, error) {
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create output directory: %w", err)
	}

	return &Profiler{
		outputDir: outputDir,
	}, nil
}

// StartCPUProfile starts CPU profiling to file
// File format: <outputDir>/<filename>
// Must call StopCPUProfile() to finalize!
//
// Example:
//
//	profiler.StartCPUProfile("cpu.prof")
//	defer profiler.StopCPUProfile()
//	// ... code to profile ...
func (p *Profiler) StartCPUProfile(filename string) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.cpuProfileFile != nil {
		return fmt.Errorf("CPU profiling already active")
	}

	path := filepath.Join(p.outputDir, filename)
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("failed to create CPU profile: %w", err)
	}

	if err := pprof.StartCPUProfile(f); err != nil {
		f.Close()
		return fmt.Errorf("failed to start CPU profile: %w", err)
	}

	p.cpuProfileFile = f
	fmt.Printf("✓ CPU profiling started: %s\n", path)
	return nil
}

// StopCPUProfile stops CPU profiling and closes file
func (p *Profiler) StopCPUProfile() {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.cpuProfileFile == nil {
		return
	}

	pprof.StopCPUProfile()
	p.cpuProfileFile.Close()
	fmt.Printf("✓ CPU profile saved: %s\n", p.cpuProfileFile.Name())
	p.cpuProfileFile = nil
}

// WriteHeapProfile writes heap memory snapshot to file
// Can be called multiple times to track memory growth
//
// Example:
//
//	profiler.WriteHeapProfile("heap_before.prof")
//	// ... allocate memory ...
//	profiler.WriteHeapProfile("heap_after.prof")
func (p *Profiler) WriteHeapProfile(filename string) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	path := filepath.Join(p.outputDir, filename)
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("failed to create heap profile: %w", err)
	}
	defer f.Close()

	runtime.GC() // Force GC to get accurate snapshot

	if err := pprof.WriteHeapProfile(f); err != nil {
		return fmt.Errorf("failed to write heap profile: %w", err)
	}

	fmt.Printf("✓ Heap profile saved: %s\n", path)
	return nil
}

// StartTrace starts execution trace to file
// Must call StopTrace() to finalize!
//
// Trace shows:
//   - Goroutine execution timeline
//   - GC pauses
//   - Network/syscall blocking
//   - Lock contention
//
// View with: go tool trace <file>
func (p *Profiler) StartTrace(filename string) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.traceFile != nil {
		return fmt.Errorf("trace already active")
	}

	path := filepath.Join(p.outputDir, filename)
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("failed to create trace file: %w", err)
	}

	if err := trace.Start(f); err != nil {
		f.Close()
		return fmt.Errorf("failed to start trace: %w", err)
	}

	p.traceFile = f
	fmt.Printf("✓ Trace started: %s\n", path)
	return nil
}

// StopTrace stops execution trace and closes file
func (p *Profiler) StopTrace() {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.traceFile == nil {
		return
	}

	trace.Stop()
	p.traceFile.Close()
	fmt.Printf("✓ Trace saved: %s\n", p.traceFile.Name())
	p.traceFile = nil
}

// WriteGoroutineProfile writes goroutine stack traces
// Useful for detecting goroutine leaks
func (p *Profiler) WriteGoroutineProfile(filename string) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	path := filepath.Join(p.outputDir, filename)
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("failed to create goroutine profile: %w", err)
	}
	defer f.Close()

	if err := pprof.Lookup("goroutine").WriteTo(f, 2); err != nil {
		return fmt.Errorf("failed to write goroutine profile: %w", err)
	}

	fmt.Printf("✓ Goroutine profile saved: %s\n", path)
	return nil
}

// WriteBlockProfile writes blocking profile
// Shows where goroutines block on synchronization primitives
// Call runtime.SetBlockProfileRate() before using!
func (p *Profiler) WriteBlockProfile(filename string) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	path := filepath.Join(p.outputDir, filename)
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("failed to create block profile: %w", err)
	}
	defer f.Close()

	if err := pprof.Lookup("block").WriteTo(f, 0); err != nil {
		return fmt.Errorf("failed to write block profile: %w", err)
	}

	fmt.Printf("✓ Block profile saved: %s\n", path)
	return nil
}

// WriteMutexProfile writes mutex contention profile
// Shows where goroutines contend on mutexes
// Call runtime.SetMutexProfileFraction() before using!
func (p *Profiler) WriteMutexProfile(filename string) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	path := filepath.Join(p.outputDir, filename)
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("failed to create mutex profile: %w", err)
	}
	defer f.Close()

	if err := pprof.Lookup("mutex").WriteTo(f, 0); err != nil {
		return fmt.Errorf("failed to write mutex profile: %w", err)
	}

	fmt.Printf("✓ Mutex profile saved: %s\n", path)
	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARK SUITE - Coordinated benchmarking with reporting
// ═══════════════════════════════════════════════════════════════════════════

// BenchmarkSuite manages multiple benchmarks
type BenchmarkSuite struct {
	benchmarks []Benchmark
	results    []BenchmarkResult
	mu         sync.Mutex
}

// Benchmark represents a single benchmark function
type Benchmark struct {
	Name        string        // Human-readable name
	Description string        // What this benchmark tests
	Fn          func() error  // Function to benchmark
	Warmups     int           // Number of warmup runs (default: 3)
	Iterations  int           // Number of measured runs (default: 10)
}

// BenchmarkResult contains benchmark measurements
type BenchmarkResult struct {
	Name         string        `json:"name"`
	Description  string        `json:"description"`
	Duration     time.Duration `json:"duration_ns"`
	DurationMS   float64       `json:"duration_ms"`
	OpsPerSec    float64       `json:"ops_per_sec"`
	AllocsPerOp  uint64        `json:"allocs_per_op"`
	BytesPerOp   uint64        `json:"bytes_per_op"`
	MinDuration  time.Duration `json:"min_duration_ns"`
	MaxDuration  time.Duration `json:"max_duration_ns"`
	StdDev       time.Duration `json:"std_dev_ns"`
	Iterations   int           `json:"iterations"`
	Timestamp    time.Time     `json:"timestamp"`
	Error        string        `json:"error,omitempty"`
}

// NewBenchmarkSuite creates empty benchmark suite
func NewBenchmarkSuite() *BenchmarkSuite {
	return &BenchmarkSuite{
		benchmarks: make([]Benchmark, 0),
		results:    make([]BenchmarkResult, 0),
	}
}

// AddBenchmark adds benchmark to suite
//
// Example:
//
//	suite.AddBenchmark("QuaternionMultiply", "Benchmark quaternion multiplication", func() error {
//	    q1 := gpu.NewQuaternion(1, 0, 0, 0)
//	    q2 := gpu.NewQuaternion(0, 1, 0, 0)
//	    _ = q1.Multiply(q2)
//	    return nil
//	})
func (bs *BenchmarkSuite) AddBenchmark(name, description string, fn func() error) {
	bs.mu.Lock()
	defer bs.mu.Unlock()

	bs.benchmarks = append(bs.benchmarks, Benchmark{
		Name:        name,
		Description: description,
		Fn:          fn,
		Warmups:     3,
		Iterations:  10,
	})
}

// AddBenchmarkWithConfig adds benchmark with custom warmup/iteration counts
func (bs *BenchmarkSuite) AddBenchmarkWithConfig(name, description string, fn func() error, warmups, iterations int) {
	bs.mu.Lock()
	defer bs.mu.Unlock()

	bs.benchmarks = append(bs.benchmarks, Benchmark{
		Name:        name,
		Description: description,
		Fn:          fn,
		Warmups:     warmups,
		Iterations:  iterations,
	})
}

// RunAll executes all benchmarks and returns results
// Uses proper warmup + measurement methodology
func (bs *BenchmarkSuite) RunAll() []BenchmarkResult {
	bs.mu.Lock()
	benchmarks := make([]Benchmark, len(bs.benchmarks))
	copy(benchmarks, bs.benchmarks)
	bs.mu.Unlock()

	results := make([]BenchmarkResult, 0, len(benchmarks))

	for _, bench := range benchmarks {
		fmt.Printf("\n🔬 Running: %s\n", bench.Name)
		fmt.Printf("   %s\n", bench.Description)

		result := bs.runBenchmark(bench)
		results = append(results, result)

		if result.Error != "" {
			fmt.Printf("   ❌ Error: %s\n", result.Error)
		} else {
			fmt.Printf("   ✓ Duration: %.3f ms\n", result.DurationMS)
			fmt.Printf("   ✓ Ops/sec: %.2f\n", result.OpsPerSec)
			fmt.Printf("   ✓ Allocs: %d/op\n", result.AllocsPerOp)
			fmt.Printf("   ✓ Memory: %d bytes/op\n", result.BytesPerOp)
		}
	}

	bs.mu.Lock()
	bs.results = results
	bs.mu.Unlock()

	return results
}

// runBenchmark executes single benchmark with proper methodology
func (bs *BenchmarkSuite) runBenchmark(bench Benchmark) BenchmarkResult {
	result := BenchmarkResult{
		Name:        bench.Name,
		Description: bench.Description,
		Timestamp:   time.Now(),
		Iterations:  bench.Iterations,
	}

	// Warmup phase
	for i := 0; i < bench.Warmups; i++ {
		if err := bench.Fn(); err != nil {
			result.Error = fmt.Sprintf("warmup failed: %v", err)
			return result
		}
	}

	// Force GC before measurement
	runtime.GC()
	time.Sleep(10 * time.Millisecond)

	// Measurement phase
	var memStatsBefore, memStatsAfter runtime.MemStats
	runtime.ReadMemStats(&memStatsBefore)

	durations := make([]time.Duration, bench.Iterations)
	var totalDuration time.Duration

	for i := 0; i < bench.Iterations; i++ {
		start := time.Now()
		if err := bench.Fn(); err != nil {
			result.Error = fmt.Sprintf("iteration %d failed: %v", i, err)
			return result
		}
		duration := time.Since(start)
		durations[i] = duration
		totalDuration += duration
	}

	runtime.ReadMemStats(&memStatsAfter)

	// Calculate statistics
	avgDuration := totalDuration / time.Duration(bench.Iterations)
	result.Duration = avgDuration
	result.DurationMS = float64(avgDuration.Nanoseconds()) / 1e6

	// Avoid division by zero or infinity for very fast operations
	if avgDuration > 0 {
		result.OpsPerSec = 1e9 / float64(avgDuration.Nanoseconds())
	} else {
		result.OpsPerSec = 0 // Too fast to measure accurately
	}

	// Memory statistics
	allocsDiff := memStatsAfter.Mallocs - memStatsBefore.Mallocs
	bytesDiff := memStatsAfter.TotalAlloc - memStatsBefore.TotalAlloc
	result.AllocsPerOp = allocsDiff / uint64(bench.Iterations)
	result.BytesPerOp = bytesDiff / uint64(bench.Iterations)

	// Min/Max/StdDev
	result.MinDuration = durations[0]
	result.MaxDuration = durations[0]
	for _, d := range durations {
		if d < result.MinDuration {
			result.MinDuration = d
		}
		if d > result.MaxDuration {
			result.MaxDuration = d
		}
	}

	// Standard deviation
	var sumSquares float64
	for _, d := range durations {
		diff := float64(d - avgDuration)
		sumSquares += diff * diff
	}
	variance := sumSquares / float64(bench.Iterations)
	result.StdDev = time.Duration(variance)

	return result
}

// GenerateReport generates human-readable benchmark report
func (bs *BenchmarkSuite) GenerateReport() string {
	bs.mu.Lock()
	results := make([]BenchmarkResult, len(bs.results))
	copy(results, bs.results)
	bs.mu.Unlock()

	if len(results) == 0 {
		return "No benchmark results available. Run benchmarks first!"
	}

	report := "\n═══════════════════════════════════════════════════════════════════════════\n"
	report += "                    ASYMMETRICA URBANLENS BENCHMARK REPORT\n"
	report += "═══════════════════════════════════════════════════════════════════════════\n\n"

	report += fmt.Sprintf("Generated: %s\n", time.Now().Format(time.RFC3339))
	report += fmt.Sprintf("Total Benchmarks: %d\n\n", len(results))

	for i, result := range results {
		report += fmt.Sprintf("─────────────────────────────────────────────────────────────────────────\n")
		report += fmt.Sprintf("[%d] %s\n", i+1, result.Name)
		report += fmt.Sprintf("    %s\n\n", result.Description)

		if result.Error != "" {
			report += fmt.Sprintf("    ❌ ERROR: %s\n", result.Error)
		} else {
			report += fmt.Sprintf("    Duration:       %.3f ms (avg over %d iterations)\n", result.DurationMS, result.Iterations)
			report += fmt.Sprintf("    Min/Max:        %.3f ms / %.3f ms\n",
				float64(result.MinDuration.Nanoseconds())/1e6,
				float64(result.MaxDuration.Nanoseconds())/1e6)
			report += fmt.Sprintf("    Throughput:     %.2f ops/sec\n", result.OpsPerSec)
			report += fmt.Sprintf("    Memory:         %d bytes/op (%d allocs/op)\n", result.BytesPerOp, result.AllocsPerOp)
		}
		report += "\n"
	}

	report += "═══════════════════════════════════════════════════════════════════════════\n"
	report += "Carmack says: \"Performance claims without profiler evidence are fiction.\"\n"
	report += "═══════════════════════════════════════════════════════════════════════════\n"

	return report
}

// SaveReportToFile writes report to text file
func (bs *BenchmarkSuite) SaveReportToFile(filename string) error {
	report := bs.GenerateReport()
	if err := os.WriteFile(filename, []byte(report), 0644); err != nil {
		return fmt.Errorf("failed to save report: %w", err)
	}
	fmt.Printf("✓ Report saved: %s\n", filename)
	return nil
}

// SaveResultsJSON saves results as JSON
func (bs *BenchmarkSuite) SaveResultsJSON(filename string) error {
	bs.mu.Lock()
	defer bs.mu.Unlock()

	data, err := json.MarshalIndent(bs.results, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal results: %w", err)
	}

	if err := os.WriteFile(filename, data, 0644); err != nil {
		return fmt.Errorf("failed to save JSON: %w", err)
	}

	fmt.Printf("✓ JSON results saved: %s\n", filename)
	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// EnableBlockProfile enables block profiling with given rate
// rate = 1 means record every blocking event
// Higher rate = sample fewer events (less overhead)
func EnableBlockProfile(rate int) {
	runtime.SetBlockProfileRate(rate)
	fmt.Printf("✓ Block profiling enabled (rate=%d)\n", rate)
}

// EnableMutexProfile enables mutex profiling with given fraction
// fraction = 1 means record every mutex event
// Higher fraction = sample fewer events
func EnableMutexProfile(fraction int) {
	runtime.SetMutexProfileFraction(fraction)
	fmt.Printf("✓ Mutex profiling enabled (fraction=%d)\n", fraction)
}

// GetMemStats returns current memory statistics
func GetMemStats() runtime.MemStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m
}

// PrintMemStats prints formatted memory statistics
func PrintMemStats() {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	fmt.Printf("\n╔═══════════════════════════════════════════════════════════════╗\n")
	fmt.Printf("║                    MEMORY STATISTICS                          ║\n")
	fmt.Printf("╠═══════════════════════════════════════════════════════════════╣\n")
	fmt.Printf("║ Alloc:          %10d MB                               ║\n", m.Alloc/1024/1024)
	fmt.Printf("║ TotalAlloc:     %10d MB                               ║\n", m.TotalAlloc/1024/1024)
	fmt.Printf("║ Sys:            %10d MB                               ║\n", m.Sys/1024/1024)
	fmt.Printf("║ NumGC:          %10d                                  ║\n", m.NumGC)
	fmt.Printf("║ Goroutines:     %10d                                  ║\n", runtime.NumGoroutine())
	fmt.Printf("╚═══════════════════════════════════════════════════════════════╝\n\n")
}
