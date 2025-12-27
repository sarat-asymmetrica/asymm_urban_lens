package profiling

import (
	"os"
	"testing"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// PERFORMANCE METRICS TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestGetMetrics_Singleton(t *testing.T) {
	// Test singleton pattern
	m1 := GetMetrics()
	m2 := GetMetrics()

	if m1 != m2 {
		t.Error("GetMetrics() should return same instance")
	}

	if m1 == nil {
		t.Error("GetMetrics() returned nil")
	}
}

func TestRecordOperation_Basic(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record some operations
	metrics.RecordOperation("test_op", 100*time.Microsecond, 256)
	metrics.RecordOperation("test_op", 150*time.Microsecond, 512)
	metrics.RecordOperation("test_op", 120*time.Microsecond, 384)

	stats := metrics.GetStats("test_op")
	if stats == nil {
		t.Fatal("Stats should not be nil")
	}

	// Verify count
	if stats.Count != 3 {
		t.Errorf("Expected count=3, got %d", stats.Count)
	}

	// Verify min/max
	if stats.MinDuration != 100*time.Microsecond {
		t.Errorf("Expected min=100μs, got %v", stats.MinDuration)
	}
	if stats.MaxDuration != 150*time.Microsecond {
		t.Errorf("Expected max=150μs, got %v", stats.MaxDuration)
	}

	// Verify average
	expectedAvg := (100 + 150 + 120) / 3
	actualAvg := stats.AvgDuration.Microseconds()
	if actualAvg != int64(expectedAvg) {
		t.Errorf("Expected avg=%dμs, got %dμs", expectedAvg, actualAvg)
	}

	// Verify memory
	expectedAvgAllocs := (256 + 512 + 384) / 3
	if stats.AvgAllocsPerOp != int64(expectedAvgAllocs) {
		t.Errorf("Expected avg allocs=%d, got %d", expectedAvgAllocs, stats.AvgAllocsPerOp)
	}
}

func TestRecordOperation_Percentiles(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record 100 operations with known distribution
	// Durations: 10μs, 20μs, 30μs, ..., 1000μs
	for i := 1; i <= 100; i++ {
		duration := time.Duration(i*10) * time.Microsecond
		metrics.RecordOperation("percentile_test", duration, 0)
	}

	stats := metrics.GetStats("percentile_test")
	if stats == nil {
		t.Fatal("Stats should not be nil")
	}

	// P50 should be ~500μs (50th element = 500μs)
	expectedP50 := 500 * time.Microsecond
	if stats.P50 != expectedP50 {
		t.Errorf("Expected P50=%v, got %v", expectedP50, stats.P50)
	}

	// P95 should be ~950μs (95th element = 950μs)
	expectedP95 := 950 * time.Microsecond
	if stats.P95 != expectedP95 {
		t.Errorf("Expected P95=%v, got %v", expectedP95, stats.P95)
	}

	// P99 should be ~990μs (99th element = 990μs)
	expectedP99 := 990 * time.Microsecond
	if stats.P99 != expectedP99 {
		t.Errorf("Expected P99=%v, got %v", expectedP99, stats.P99)
	}
}

func TestRecordOperation_Throughput(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record operations at 1M ops/sec (1μs per op)
	for i := 0; i < 10; i++ {
		metrics.RecordOperation("throughput_test", 1*time.Microsecond, 0)
	}

	stats := metrics.GetStats("throughput_test")
	if stats == nil {
		t.Fatal("Stats should not be nil")
	}

	// 1μs per op = 1M ops/sec
	expectedOpsPerSec := 1_000_000.0
	tolerance := 0.01 // 1% tolerance

	diff := (stats.OpsPerSecond - expectedOpsPerSec) / expectedOpsPerSec
	if diff < -tolerance || diff > tolerance {
		t.Errorf("Expected ops/sec≈%.2f M, got %.2f M (%.1f%% off)",
			expectedOpsPerSec/1e6, stats.OpsPerSecond/1e6, diff*100)
	}
}

func TestRecordOperation_MultipleOperations(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record different operations
	metrics.RecordOperation("op_a", 100*time.Microsecond, 256)
	metrics.RecordOperation("op_b", 200*time.Microsecond, 512)
	metrics.RecordOperation("op_a", 150*time.Microsecond, 384)

	statsA := metrics.GetStats("op_a")
	statsB := metrics.GetStats("op_b")

	if statsA == nil || statsB == nil {
		t.Fatal("Stats should not be nil")
	}

	if statsA.Count != 2 {
		t.Errorf("Expected op_a count=2, got %d", statsA.Count)
	}

	if statsB.Count != 1 {
		t.Errorf("Expected op_b count=1, got %d", statsB.Count)
	}
}

func TestRecordOperation_DisabledMetrics(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Disable()

	// Record operation while disabled
	metrics.RecordOperation("disabled_test", 100*time.Microsecond, 256)

	stats := metrics.GetStats("disabled_test")
	if stats != nil {
		t.Error("Stats should be nil when metrics disabled")
	}

	// Re-enable and verify
	metrics.Enable()
	metrics.RecordOperation("enabled_test", 100*time.Microsecond, 256)

	stats = metrics.GetStats("enabled_test")
	if stats == nil {
		t.Error("Stats should exist when metrics enabled")
	}
}

func TestGetAllStats(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record multiple operations
	metrics.RecordOperation("op1", 100*time.Microsecond, 0)
	metrics.RecordOperation("op2", 200*time.Microsecond, 0)
	metrics.RecordOperation("op3", 300*time.Microsecond, 0)

	allStats := metrics.GetAllStats()

	if len(allStats) != 3 {
		t.Errorf("Expected 3 operations, got %d", len(allStats))
	}

	expectedOps := map[string]bool{
		"op1": true,
		"op2": true,
		"op3": true,
	}

	for name := range allStats {
		if !expectedOps[name] {
			t.Errorf("Unexpected operation: %s", name)
		}
	}
}

func TestDefaultTargets(t *testing.T) {
	metrics := GetMetrics()

	// Verify default targets exist
	expectedTargets := []string{
		"vqc_engine",
		"williams_batch",
		"quaternion_multiply",
		"quaternion_slerp",
		"gpu_batch_multiply",
		"gpu_batch_slerp",
		"semantic_similarity",
		"digital_root",
	}

	for _, name := range expectedTargets {
		target := metrics.GetTarget(name)
		if target == nil {
			t.Errorf("Default target missing: %s", name)
		}
	}

	// Verify VQC target
	vqcTarget := metrics.GetTarget("vqc_engine")
	if vqcTarget == nil {
		t.Fatal("VQC target should exist")
	}

	if vqcTarget.TargetOpsPerSec != 71_000_000 {
		t.Errorf("Expected VQC target=71M ops/sec, got %.2f M",
			vqcTarget.TargetOpsPerSec/1e6)
	}
}

func TestRegisterCustomTarget(t *testing.T) {
	metrics := GetMetrics()

	customTarget := &PerformanceTarget{
		Name:            "custom_operation",
		TargetOpsPerSec: 5_000_000,
		TargetP95:       200 * time.Nanosecond,
		TargetP99:       400 * time.Nanosecond,
		Description:     "Custom test operation",
	}

	metrics.RegisterTarget(customTarget)

	retrieved := metrics.GetTarget("custom_operation")
	if retrieved == nil {
		t.Fatal("Custom target should exist")
	}

	if retrieved.Name != customTarget.Name {
		t.Errorf("Expected name=%s, got %s", customTarget.Name, retrieved.Name)
	}

	if retrieved.TargetOpsPerSec != customTarget.TargetOpsPerSec {
		t.Errorf("Expected ops/sec=%.2f M, got %.2f M",
			customTarget.TargetOpsPerSec/1e6, retrieved.TargetOpsPerSec/1e6)
	}
}

func TestGenerateReport_Basic(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record some operations
	for i := 0; i < 100; i++ {
		metrics.RecordOperation("vqc_engine", 14*time.Nanosecond, 0) // At target!
	}

	report := metrics.GenerateReport()

	if report == nil {
		t.Fatal("Report should not be nil")
	}

	if report.Summary.TotalOperations != 1 {
		t.Errorf("Expected 1 operation, got %d", report.Summary.TotalOperations)
	}

	if report.Summary.TotalSamples != 100 {
		t.Errorf("Expected 100 samples, got %d", report.Summary.TotalSamples)
	}

	// Should be EXCELLENT since at target
	if report.Summary.ExcellentCount != 1 {
		t.Errorf("Expected 1 excellent operation, got %d", report.Summary.ExcellentCount)
	}
}

func TestGenerateReport_GapAnalysis(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record VQC engine running at 50% of target (critical!)
	targetOps := 71_000_000.0
	actualDuration := time.Duration(float64(time.Second) / (targetOps * 0.5))

	for i := 0; i < 100; i++ {
		metrics.RecordOperation("vqc_engine", actualDuration, 0)
	}

	report := metrics.GenerateReport()
	opReport := report.Operations["vqc_engine"]

	if opReport == nil {
		t.Fatal("VQC operation report should exist")
	}

	// Should be CRITICAL (50% of target)
	if opReport.Status != "CRITICAL" {
		t.Errorf("Expected CRITICAL status, got %s", opReport.Status)
	}

	// Gap should be approximately -50%
	expectedGap := -50.0
	tolerance := 5.0 // 5% tolerance

	if opReport.ThroughputGap < expectedGap-tolerance || opReport.ThroughputGap > expectedGap+tolerance {
		t.Errorf("Expected gap≈%.1f%%, got %.1f%%", expectedGap, opReport.ThroughputGap)
	}

	// Should have recommendations
	if len(opReport.Recommendations) == 0 {
		t.Error("Expected recommendations for critical performance")
	}
}

func TestGenerateReport_StatusClassification(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	target := &PerformanceTarget{
		Name:            "test_classification",
		TargetOpsPerSec: 1_000_000,
		TargetP95:       1000 * time.Nanosecond,
		TargetP99:       2000 * time.Nanosecond,
		Description:     "Test status classification",
	}
	metrics.RegisterTarget(target)

	testCases := []struct {
		name           string
		opsPerSec      float64
		expectedStatus string
	}{
		{"excellent", 1_100_000, "EXCELLENT"},  // 110% of target
		{"good", 850_000, "GOOD"},              // 85% of target
		{"needs_work", 600_000, "NEEDS_WORK"},  // 60% of target
		{"critical", 400_000, "CRITICAL"},      // 40% of target
	}

	for _, tc := range testCases {
		metrics.Reset()

		duration := time.Duration(float64(time.Second) / tc.opsPerSec)
		for i := 0; i < 100; i++ {
			metrics.RecordOperation("test_classification", duration, 0)
		}

		report := metrics.GenerateReport()
		opReport := report.Operations["test_classification"]

		if opReport.Status != tc.expectedStatus {
			t.Errorf("Test %s: Expected status=%s, got %s",
				tc.name, tc.expectedStatus, opReport.Status)
		}
	}
}

func TestExportJSON(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record some data
	for i := 0; i < 100; i++ {
		metrics.RecordOperation("test_export", 100*time.Nanosecond, 256)
	}

	report := metrics.GenerateReport()

	// Export to temporary file
	tmpfile := "test_report.json"
	defer os.Remove(tmpfile)

	err := report.ExportJSON(tmpfile)
	if err != nil {
		t.Fatalf("ExportJSON failed: %v", err)
	}

	// Verify file exists
	if _, err := os.Stat(tmpfile); os.IsNotExist(err) {
		t.Error("JSON file was not created")
	}

	// Verify file has content
	data, err := os.ReadFile(tmpfile)
	if err != nil {
		t.Fatalf("Failed to read JSON file: %v", err)
	}

	if len(data) == 0 {
		t.Error("JSON file is empty")
	}
}

func TestExportMarkdown(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Record some data
	for i := 0; i < 100; i++ {
		metrics.RecordOperation("test_markdown", 100*time.Nanosecond, 256)
	}

	report := metrics.GenerateReport()

	// Export to temporary file
	tmpfile := "test_report.md"
	defer os.Remove(tmpfile)

	err := report.ExportMarkdown(tmpfile)
	if err != nil {
		t.Fatalf("ExportMarkdown failed: %v", err)
	}

	// Verify file exists
	if _, err := os.Stat(tmpfile); os.IsNotExist(err) {
		t.Error("Markdown file was not created")
	}

	// Verify file has content
	data, err := os.ReadFile(tmpfile)
	if err != nil {
		t.Fatalf("Failed to read Markdown file: %v", err)
	}

	if len(data) == 0 {
		t.Error("Markdown file is empty")
	}

	// Verify contains expected headers
	content := string(data)
	expectedHeaders := []string{
		"# Performance Report",
		"## Summary",
		"## Operation Details",
	}

	for _, header := range expectedHeaders {
		if !contains(content, header) {
			t.Errorf("Markdown missing expected header: %s", header)
		}
	}
}

func TestTimedOperation(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Test timed operation wrapper
	expectedResult := 42
	result, err := TimedOperation("timed_test", func() (interface{}, error) {
		time.Sleep(1 * time.Millisecond)
		return expectedResult, nil
	})

	if err != nil {
		t.Fatalf("TimedOperation returned error: %v", err)
	}

	if result.(int) != expectedResult {
		t.Errorf("Expected result=%d, got %d", expectedResult, result)
	}

	// Verify metrics were recorded
	stats := metrics.GetStats("timed_test")
	if stats == nil {
		t.Fatal("Stats should exist for timed operation")
	}

	if stats.Count != 1 {
		t.Errorf("Expected count=1, got %d", stats.Count)
	}

	if stats.AvgDuration < 1*time.Millisecond {
		t.Errorf("Expected duration≥1ms, got %v", stats.AvgDuration)
	}
}

func TestConcurrentRecording(t *testing.T) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Test thread safety with concurrent recordings
	const numGoroutines = 10
	const recordsPerGoroutine = 100

	done := make(chan bool, numGoroutines)

	for i := 0; i < numGoroutines; i++ {
		go func() {
			for j := 0; j < recordsPerGoroutine; j++ {
				metrics.RecordOperation("concurrent_test", 100*time.Nanosecond, 256)
			}
			done <- true
		}()
	}

	// Wait for all goroutines
	for i := 0; i < numGoroutines; i++ {
		<-done
	}

	stats := metrics.GetStats("concurrent_test")
	if stats == nil {
		t.Fatal("Stats should exist")
	}

	expectedCount := numGoroutines * recordsPerGoroutine
	if stats.Count != int64(expectedCount) {
		t.Errorf("Expected count=%d, got %d", expectedCount, stats.Count)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkRecordOperation(b *testing.B) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		metrics.RecordOperation("benchmark_op", 100*time.Nanosecond, 256)
	}
}

func BenchmarkRecordOperation_Disabled(b *testing.B) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Disable()

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		metrics.RecordOperation("benchmark_op", 100*time.Nanosecond, 256)
	}
}

func BenchmarkGetStats(b *testing.B) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Pre-populate
	for i := 0; i < 1000; i++ {
		metrics.RecordOperation("bench_stats", 100*time.Nanosecond, 0)
	}

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		_ = metrics.GetStats("bench_stats")
	}
}

func BenchmarkGenerateReport(b *testing.B) {
	metrics := GetMetrics()
	metrics.Reset()
	metrics.Enable()

	// Pre-populate with multiple operations
	for i := 0; i < 100; i++ {
		metrics.RecordOperation("op1", 100*time.Nanosecond, 0)
		metrics.RecordOperation("op2", 200*time.Nanosecond, 0)
		metrics.RecordOperation("op3", 300*time.Nanosecond, 0)
	}

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		_ = metrics.GenerateReport()
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && containsHelper(s, substr))
}

func containsHelper(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
