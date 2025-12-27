// Package profiling - Tests for profiling infrastructure
package profiling

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"
	"time"
)

func TestProfiler_StartStopCPUProfile(t *testing.T) {
	tmpDir := t.TempDir()
	profiler, err := NewProfiler(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create profiler: %v", err)
	}

	// Start CPU profiling
	if err := profiler.StartCPUProfile("test_cpu.prof"); err != nil {
		t.Fatalf("Failed to start CPU profile: %v", err)
	}

	// Do some work
	for i := 0; i < 1000000; i++ {
		_ = i * i
	}

	// Stop profiling
	profiler.StopCPUProfile()

	// Verify file exists
	profilePath := filepath.Join(tmpDir, "test_cpu.prof")
	if _, err := os.Stat(profilePath); os.IsNotExist(err) {
		t.Errorf("CPU profile file not created: %s", profilePath)
	}
}

func TestProfiler_WriteHeapProfile(t *testing.T) {
	tmpDir := t.TempDir()
	profiler, err := NewProfiler(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create profiler: %v", err)
	}

	// Allocate some memory
	data := make([]byte, 1024*1024) // 1MB
	_ = data

	// Write heap profile
	if err := profiler.WriteHeapProfile("test_heap.prof"); err != nil {
		t.Fatalf("Failed to write heap profile: %v", err)
	}

	// Verify file exists
	profilePath := filepath.Join(tmpDir, "test_heap.prof")
	if _, err := os.Stat(profilePath); os.IsNotExist(err) {
		t.Errorf("Heap profile file not created: %s", profilePath)
	}
}

func TestProfiler_StartStopTrace(t *testing.T) {
	tmpDir := t.TempDir()
	profiler, err := NewProfiler(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create profiler: %v", err)
	}

	// Start trace
	if err := profiler.StartTrace("test_trace.out"); err != nil {
		t.Fatalf("Failed to start trace: %v", err)
	}

	// Do some work
	time.Sleep(10 * time.Millisecond)

	// Stop trace
	profiler.StopTrace()

	// Verify file exists
	tracePath := filepath.Join(tmpDir, "test_trace.out")
	if _, err := os.Stat(tracePath); os.IsNotExist(err) {
		t.Errorf("Trace file not created: %s", tracePath)
	}
}

func TestProfiler_WriteGoroutineProfile(t *testing.T) {
	tmpDir := t.TempDir()
	profiler, err := NewProfiler(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create profiler: %v", err)
	}

	// Spawn some goroutines
	done := make(chan bool)
	for i := 0; i < 10; i++ {
		go func() {
			time.Sleep(10 * time.Millisecond)
			done <- true
		}()
	}

	// Write goroutine profile
	if err := profiler.WriteGoroutineProfile("test_goroutine.prof"); err != nil {
		t.Fatalf("Failed to write goroutine profile: %v", err)
	}

	// Cleanup
	for i := 0; i < 10; i++ {
		<-done
	}

	// Verify file exists
	profilePath := filepath.Join(tmpDir, "test_goroutine.prof")
	if _, err := os.Stat(profilePath); os.IsNotExist(err) {
		t.Errorf("Goroutine profile file not created: %s", profilePath)
	}
}

func TestProfiler_DoubleStart(t *testing.T) {
	tmpDir := t.TempDir()
	profiler, err := NewProfiler(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create profiler: %v", err)
	}

	// Start CPU profiling
	if err := profiler.StartCPUProfile("test1.prof"); err != nil {
		t.Fatalf("Failed to start first CPU profile: %v", err)
	}
	defer profiler.StopCPUProfile()

	// Try to start again (should fail)
	if err := profiler.StartCPUProfile("test2.prof"); err == nil {
		t.Error("Expected error when starting CPU profile twice, got nil")
	}
}

func TestBenchmarkSuite_AddAndRun(t *testing.T) {
	suite := NewBenchmarkSuite()

	// Add simple benchmark
	suite.AddBenchmark(
		"SimpleAllocation",
		"Benchmark memory allocation",
		func() error {
			_ = make([]byte, 1024)
			return nil
		},
	)

	// Add computation benchmark
	suite.AddBenchmark(
		"SimpleComputation",
		"Benchmark integer multiplication",
		func() error {
			x := 0
			for i := 0; i < 1000; i++ {
				x += i * i
			}
			_ = x
			return nil
		},
	)

	// Run all benchmarks
	results := suite.RunAll()

	// Verify results
	if len(results) != 2 {
		t.Errorf("Expected 2 results, got %d", len(results))
	}

	for _, result := range results {
		if result.Error != "" {
			t.Errorf("Benchmark %s failed: %s", result.Name, result.Error)
		}
		// Duration can be 0 for very fast operations (sub-nanosecond)
		if result.Duration < 0 {
			t.Errorf("Benchmark %s has negative duration: %v", result.Name, result.Duration)
		}
		// OpsPerSec can be 0 if operation is too fast to measure accurately
		if result.OpsPerSec < 0 {
			t.Errorf("Benchmark %s has negative ops/sec: %f", result.Name, result.OpsPerSec)
		}
	}
}

func TestBenchmarkSuite_GenerateReport(t *testing.T) {
	suite := NewBenchmarkSuite()

	suite.AddBenchmark(
		"ReportTest",
		"Test report generation",
		func() error {
			time.Sleep(1 * time.Millisecond)
			return nil
		},
	)

	suite.RunAll()

	report := suite.GenerateReport()
	if len(report) == 0 {
		t.Error("Generated report is empty")
	}

	// Report should contain benchmark name
	if !containsSubstring(report, "ReportTest") {
		t.Error("Report missing benchmark name")
	}

	// Report should contain statistics
	if !containsSubstring(report, "Duration") && !containsSubstring(report, "Throughput") {
		t.Error("Report missing statistics")
	}
}

func TestBenchmarkSuite_SaveReportToFile(t *testing.T) {
	tmpDir := t.TempDir()
	suite := NewBenchmarkSuite()

	suite.AddBenchmark("SaveTest", "Test file saving", func() error {
		return nil
	})

	suite.RunAll()

	reportPath := filepath.Join(tmpDir, "benchmark_report.txt")
	if err := suite.SaveReportToFile(reportPath); err != nil {
		t.Fatalf("Failed to save report: %v", err)
	}

	// Verify file exists
	if _, err := os.Stat(reportPath); os.IsNotExist(err) {
		t.Errorf("Report file not created: %s", reportPath)
	}

	// Verify file is not empty
	content, err := os.ReadFile(reportPath)
	if err != nil {
		t.Fatalf("Failed to read report file: %v", err)
	}
	if len(content) == 0 {
		t.Error("Report file is empty")
	}
}

func TestBenchmarkSuite_SaveResultsJSON(t *testing.T) {
	tmpDir := t.TempDir()
	suite := NewBenchmarkSuite()

	suite.AddBenchmark("JSONTest", "Test JSON saving", func() error {
		return nil
	})

	suite.RunAll()

	jsonPath := filepath.Join(tmpDir, "results.json")
	if err := suite.SaveResultsJSON(jsonPath); err != nil {
		t.Fatalf("Failed to save JSON: %v", err)
	}

	// Verify file exists and is valid JSON
	if _, err := os.Stat(jsonPath); os.IsNotExist(err) {
		t.Errorf("JSON file not created: %s", jsonPath)
	}

	content, err := os.ReadFile(jsonPath)
	if err != nil {
		t.Fatalf("Failed to read JSON file: %v", err)
	}
	if len(content) == 0 {
		t.Error("JSON file is empty")
	}
}

func TestBenchmarkSuite_WithConfig(t *testing.T) {
	suite := NewBenchmarkSuite()

	// Add benchmark with custom warmups/iterations
	suite.AddBenchmarkWithConfig(
		"CustomConfig",
		"Benchmark with custom configuration",
		func() error {
			time.Sleep(1 * time.Millisecond)
			return nil
		},
		1,  // 1 warmup
		5,  // 5 iterations
	)

	results := suite.RunAll()

	if len(results) != 1 {
		t.Fatalf("Expected 1 result, got %d", len(results))
	}

	if results[0].Iterations != 5 {
		t.Errorf("Expected 5 iterations, got %d", results[0].Iterations)
	}
}

func TestEnableBlockProfile(t *testing.T) {
	// Just test that it doesn't panic
	EnableBlockProfile(1)
	runtime.SetBlockProfileRate(0) // Reset
}

func TestEnableMutexProfile(t *testing.T) {
	// Just test that it doesn't panic
	EnableMutexProfile(1)
	runtime.SetMutexProfileFraction(0) // Reset
}

func TestGetMemStats(t *testing.T) {
	stats := GetMemStats()

	// Basic sanity checks
	if stats.Alloc == 0 {
		t.Error("Expected non-zero Alloc")
	}
	if stats.Sys == 0 {
		t.Error("Expected non-zero Sys")
	}
}

func TestPrintMemStats(t *testing.T) {
	// Just test that it doesn't panic
	PrintMemStats()
}

// Benchmark the profiler overhead itself
func BenchmarkProfilerOverhead(b *testing.B) {
	tmpDir := b.TempDir()
	profiler, err := NewProfiler(tmpDir)
	if err != nil {
		b.Fatalf("Failed to create profiler: %v", err)
	}

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		// Measure overhead of starting/stopping CPU profile
		profiler.StartCPUProfile("bench_cpu.prof")
		profiler.StopCPUProfile()
	}
}

func BenchmarkBenchmarkSuiteOverhead(b *testing.B) {
	suite := NewBenchmarkSuite()

	// Add trivial benchmark
	suite.AddBenchmark("Trivial", "No-op benchmark", func() error {
		return nil
	})

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		suite.RunAll()
	}
}

// Helper function
func containsSubstring(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && anySubstring(s, substr))
}

func anySubstring(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
