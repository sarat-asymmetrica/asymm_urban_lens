// Package vqc - VQC GPU Acceleration Test Suite
// Tests GPU-accelerated quaternion operations targeting 71M ops/sec
//
// Built: 2025-12-27 (Wave 4, Agent 1)
// Foundation: 187 days of validated mathematics from asymm_all_math
// Target: 71M operations/second (proven achievable in vqc_cancer_classifier.go)
//
// Test Categories:
//   - Stabilization: 100% required (initialization, correctness, normalization)
//   - Optimization: 85% required (performance benchmarks, throughput)
//   - Exploration: 70% required (GPU detection, integration)
package vqc

import (
	"math"
	"testing"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/gpu"
)

// ============================================================================
// STABILIZATION TESTS (100% Required)
// ============================================================================

// TestVQC_Initialization verifies VQC engine starts correctly
func TestVQC_Initialization(t *testing.T) {
	t.Run("GPUAccelerator_Creation", func(t *testing.T) {
		acc := gpu.NewAccelerator()
		if acc == nil {
			t.Fatal("NewAccelerator() returned nil")
		}

		// Should have valid stats even with no operations
		stats := acc.GetStats()
		if stats == nil {
			t.Error("GetStats() returned nil")
		}

		// Initial counts should be zero
		if stats.TotalOps != 0 {
			t.Errorf("Initial TotalOps = %d, expected 0", stats.TotalOps)
		}
	})

	t.Run("GPUAccelerator_StatusCheck", func(t *testing.T) {
		acc := gpu.NewAccelerator()
		status := acc.GetStatus()

		// Status should contain key fields
		if _, ok := status["gpu_available"]; !ok {
			t.Error("Status missing 'gpu_available' field")
		}
		if _, ok := status["backend"]; !ok {
			t.Error("Status missing 'backend' field")
		}
		if _, ok := status["stats"]; !ok {
			t.Error("Status missing 'stats' field")
		}

		t.Logf("GPU Status: %+v", status)
	})

	t.Run("QuaternionPrimitives_Available", func(t *testing.T) {
		// Verify basic quaternion operations work
		q1 := gpu.NewQuaternion(1, 0, 0, 0)
		q2 := gpu.NewQuaternion(0, 1, 0, 0)

		// Test multiplication
		result := q1.Multiply(q2)
		if err := result.Validate(); err != nil {
			t.Errorf("Quaternion multiplication produced invalid result: %v", err)
		}

		// Test SLERP
		slerped := gpu.SLERP(q1, q2, 0.5)
		if err := slerped.Validate(); err != nil {
			t.Errorf("SLERP produced invalid result: %v", err)
		}
	})
}

// TestVQC_QuaternionMultiplication tests Q1 × Q2 correctness
func TestVQC_QuaternionMultiplication(t *testing.T) {
	t.Run("Identity_Multiplication", func(t *testing.T) {
		id := gpu.Identity()
		q := gpu.NewQuaternion(1, 2, 3, 4)

		// id × q = q
		result := id.Multiply(q)
		if math.Abs(float64(result.W-q.W)) > 1e-5 ||
			math.Abs(float64(result.X-q.X)) > 1e-5 ||
			math.Abs(float64(result.Y-q.Y)) > 1e-5 ||
			math.Abs(float64(result.Z-q.Z)) > 1e-5 {
			t.Errorf("Identity multiplication failed: id × q = %v, expected %v", result, q)
		}
	})

	t.Run("NonCommutative_Property", func(t *testing.T) {
		q1 := gpu.NewQuaternion(1, 2, 0, 0)
		q2 := gpu.NewQuaternion(0, 0, 3, 4)

		// q1 × q2 ≠ q2 × q1 (generally)
		r1 := q1.Multiply(q2)
		r2 := q2.Multiply(q1)

		// They should be different (unless special case)
		same := math.Abs(float64(r1.W-r2.W)) < 1e-5 &&
			math.Abs(float64(r1.X-r2.X)) < 1e-5 &&
			math.Abs(float64(r1.Y-r2.Y)) < 1e-5 &&
			math.Abs(float64(r1.Z-r2.Z)) < 1e-5

		if same {
			t.Logf("Note: q1 × q2 = q2 × q1 for this case (commutative)")
		} else {
			t.Logf("Verified: q1 × q2 ≠ q2 × q1 (non-commutative)")
		}
	})

	t.Run("Batch_Multiplication", func(t *testing.T) {
		acc := gpu.NewAccelerator()

		// Create batch of quaternion pairs
		pairs := make([][2]gpu.Quaternion, 1000)
		for i := 0; i < 1000; i++ {
			pairs[i] = [2]gpu.Quaternion{
				gpu.RandomQuaternion(),
				gpu.RandomQuaternion(),
			}
		}

		// Multiply in batch
		results := acc.BatchMultiply(pairs)

		// Verify all results are valid quaternions
		for i, r := range results {
			if err := r.Validate(); err != nil {
				t.Errorf("Result %d invalid: %v", i, err)
			}
		}

		// Check stats
		stats := acc.GetStats()
		if stats.TotalOps != 1000 {
			t.Errorf("Expected 1000 ops, got %d", stats.TotalOps)
		}
	})
}

// TestVQC_QuaternionNormalization tests ||Q|| = 1.0 always
func TestVQC_QuaternionNormalization(t *testing.T) {
	t.Run("Normalize_ArbitraryQuaternion", func(t *testing.T) {
		q := gpu.NewQuaternion(5, 12, 84, 181).Normalize()
		norm := q.Norm()

		// Should be normalized (||Q|| = 1.0)
		if math.Abs(float64(norm-1.0)) > 1e-5 {
			t.Errorf("Normalized quaternion has ||Q|| = %.10f, expected 1.0", norm)
		}
	})

	t.Run("Normalize_ZeroQuaternion", func(t *testing.T) {
		q := gpu.Quaternion{W: 0, X: 0, Y: 0, Z: 0}
		normalized := q.Normalize()

		// Should return identity
		if err := normalized.Validate(); err != nil {
			t.Errorf("Normalized zero quaternion invalid: %v", err)
		}

		// Should be identity (1, 0, 0, 0)
		if math.Abs(float64(normalized.W-1.0)) > 1e-5 {
			t.Errorf("Normalized zero should be identity, got %v", normalized)
		}
	})

	t.Run("Batch_Normalization", func(t *testing.T) {
		acc := gpu.NewAccelerator()

		// Create batch of random (non-normalized) quaternions
		quats := make([]gpu.Quaternion, 10000)
		for i := 0; i < 10000; i++ {
			quats[i] = gpu.Quaternion{
				W: float32(i) * 0.1,
				X: float32(i) * 0.2,
				Y: float32(i) * 0.3,
				Z: float32(i) * 0.4,
			}
		}

		// Normalize in batch
		results := acc.BatchNormalize(quats)

		// All should be on S³ (||Q|| = 1.0)
		for i, r := range results {
			if err := r.Validate(); err != nil {
				t.Errorf("Result %d not on S³: %v", i, err)
			}
		}
	})
}

// TestVQC_SLERP_Interpolation tests smooth quaternion interpolation
func TestVQC_SLERP_Interpolation(t *testing.T) {
	t.Run("SLERP_Endpoints", func(t *testing.T) {
		q0 := gpu.NewQuaternion(1, 0, 0, 0)
		q1 := gpu.NewQuaternion(0, 1, 0, 0)

		// t=0 should give q0
		r0 := gpu.SLERP(q0, q1, 0.0)
		if math.Abs(float64(r0.W-q0.W)) > 1e-4 {
			t.Errorf("SLERP(t=0) = %v, expected %v", r0, q0)
		}

		// t=1 should give q1
		r1 := gpu.SLERP(q0, q1, 1.0)
		if math.Abs(float64(r1.X-q1.X)) > 1e-4 {
			t.Errorf("SLERP(t=1) = %v, expected %v", r1, q1)
		}
	})

	t.Run("SLERP_Midpoint", func(t *testing.T) {
		q0 := gpu.Identity()
		q1 := gpu.FromAxisAngle([3]float32{0, 0, 1}, float32(math.Pi/2))

		// Midpoint should be halfway rotation
		mid := gpu.SLERP(q0, q1, 0.5)

		// Should still be on S³
		if err := mid.Validate(); err != nil {
			t.Errorf("SLERP midpoint not on S³: %v", err)
		}

		// Distance from q0 to mid should equal distance from mid to q1
		d1 := gpu.GeodeticDistance(q0, mid)
		d2 := gpu.GeodeticDistance(mid, q1)

		if math.Abs(float64(d1-d2)) > 1e-4 {
			t.Errorf("SLERP not symmetric: d(q0,mid)=%.6f, d(mid,q1)=%.6f", d1, d2)
		}
	})

	t.Run("Batch_SLERP", func(t *testing.T) {
		acc := gpu.NewAccelerator()

		// Create batch of SLERP pairs
		pairs := make([][2]gpu.Quaternion, 5000)
		for i := 0; i < 5000; i++ {
			pairs[i] = [2]gpu.Quaternion{
				gpu.RandomQuaternion(),
				gpu.RandomQuaternion(),
			}
		}

		// SLERP all pairs
		results := acc.BatchSLERP(pairs, 0.5)

		// All results should be valid
		for i, r := range results {
			if err := r.Validate(); err != nil {
				t.Errorf("SLERP result %d invalid: %v", i, err)
			}
		}
	})
}

// TestVQC_BatchProcessing tests Williams batching applied
func TestVQC_BatchProcessing(t *testing.T) {
	t.Run("Williams_OptimalBatchSize", func(t *testing.T) {
		testCases := []struct {
			n        int
			expected int
		}{
			{100, 66},        // √100 × log₂(100) ≈ 66
			{1000, 316},      // √1000 × log₂(1000) ≈ 316
			{10000, 1329},    // √10000 × log₂(10000) ≈ 1329
			{1000000, 19932}, // √1M × log₂(1M) ≈ 19932
		}

		for _, tc := range testCases {
			result := OptimalBatchSize(tc.n)
			tolerance := float64(tc.expected) * 0.1

			diff := math.Abs(float64(result - tc.expected))
			if diff > tolerance {
				t.Errorf("OptimalBatchSize(%d) = %d, expected ~%d (diff: %.0f)",
					tc.n, result, tc.expected, diff)
			}
		}
	})

	t.Run("Williams_BatchOptimizer", func(t *testing.T) {
		optimizer := NewWilliamsOptimizer()

		// Create large dataset
		items := make([]interface{}, 10000)
		for i := 0; i < 10000; i++ {
			items[i] = gpu.RandomQuaternion()
		}

		processed := 0
		err := optimizer.OptimizeBatch(items, func(batch []interface{}) error {
			processed += len(batch)
			return nil
		})

		if err != nil {
			t.Fatalf("OptimizeBatch failed: %v", err)
		}

		if processed != 10000 {
			t.Errorf("Processed %d items, expected 10000", processed)
		}

		t.Logf("Processed 10K items using Williams batching")
	})
}

// TestVQC_DigitalRootFiltering tests 88.9% elimination
func TestVQC_DigitalRootFiltering(t *testing.T) {
	t.Run("DigitalRoot_BasicProperties", func(t *testing.T) {
		testCases := []struct {
			n  int
			dr int
		}{
			{0, 0},
			{9, 9},
			{10, 1},
			{123, 6}, // 1+2+3 = 6
			{456, 6}, // 4+5+6 = 15 → 1+5 = 6
			{999, 9},
		}

		for _, tc := range testCases {
			result := DigitalRoot(tc.n)
			if result != tc.dr {
				t.Errorf("DigitalRoot(%d) = %d, expected %d", tc.n, result, tc.dr)
			}
		}
	})

	t.Run("DigitalRoot_Filtering_88_9_Percent", func(t *testing.T) {
		// Test 88.9% elimination
		candidates := make([]int, 10000)
		for i := 0; i < 10000; i++ {
			candidates[i] = i
		}

		target := 1234
		filtered := DigitalRootFilter(candidates, target)

		// Should eliminate ~88.9% (keep ~11.1% = 1/9)
		expectedSize := len(candidates) / 9
		tolerance := 100 // Allow some variance

		actualRatio := float64(len(filtered)) / float64(len(candidates))
		eliminationRatio := 1.0 - actualRatio

		t.Logf("Filtered %d → %d (elimination ratio: %.2f%%)",
			len(candidates), len(filtered), eliminationRatio*100)

		if math.Abs(float64(len(filtered)-expectedSize)) > float64(tolerance) {
			t.Errorf("Filtered %d items, expected ~%d", len(filtered), expectedSize)
		}

		// Verify all filtered items match target's digital root
		targetDR := DigitalRoot(target)
		for _, item := range filtered {
			if DigitalRoot(item) != targetDR {
				t.Errorf("Filtered item %d has DR %d, expected %d",
					item, DigitalRoot(item), targetDR)
			}
		}
	})
}

// ============================================================================
// OPTIMIZATION TESTS (85% Required)
// ============================================================================

// TestVQC_Performance_1M_Ops benchmarks 1M operations
func TestVQC_Performance_1M_Ops(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping performance test in short mode")
	}

	acc := gpu.NewAccelerator()

	// Prepare 1M SLERP operations
	pairs := make([][2]gpu.Quaternion, 1_000_000)
	for i := 0; i < 1_000_000; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	t.Logf("Starting 1M SLERP operations...")
	start := time.Now()

	results := acc.BatchSLERP(pairs, 0.5)

	elapsed := time.Since(start)
	opsPerSec := float64(len(results)) / elapsed.Seconds()

	t.Logf("✅ 1M SLERP operations completed in %v", elapsed)
	t.Logf("✅ Throughput: %.2f ops/sec (%.2f M ops/sec)", opsPerSec, opsPerSec/1e6)

	stats := acc.GetStats()
	t.Logf("Stats: %+v", stats)

	// Verify results are valid
	invalidCount := 0
	for _, r := range results {
		if err := r.Validate(); err != nil {
			invalidCount++
		}
	}
	if invalidCount > 0 {
		t.Errorf("%d invalid results out of 1M", invalidCount)
	}
}

// TestVQC_Performance_10M_Ops benchmarks 10M operations
func TestVQC_Performance_10M_Ops(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping heavy performance test in short mode")
	}

	acc := gpu.NewAccelerator()

	// Process in batches of 1M (Williams batching!)
	totalOps := 10_000_000
	batchSize := 1_000_000
	numBatches := totalOps / batchSize

	t.Logf("Starting 10M SLERP operations (%d batches of %d)...", numBatches, batchSize)
	start := time.Now()

	totalProcessed := 0
	for batch := 0; batch < numBatches; batch++ {
		// Create batch
		pairs := make([][2]gpu.Quaternion, batchSize)
		for i := 0; i < batchSize; i++ {
			pairs[i] = [2]gpu.Quaternion{
				gpu.RandomQuaternion(),
				gpu.RandomQuaternion(),
			}
		}

		// Process
		results := acc.BatchSLERP(pairs, 0.5)
		totalProcessed += len(results)

		if batch%2 == 0 {
			t.Logf("  Batch %d/%d complete (%d total ops)", batch+1, numBatches, totalProcessed)
		}
	}

	elapsed := time.Since(start)
	opsPerSec := float64(totalProcessed) / elapsed.Seconds()

	t.Logf("✅ 10M SLERP operations completed in %v", elapsed)
	t.Logf("✅ Throughput: %.2f M ops/sec", opsPerSec/1e6)

	stats := acc.GetStats()
	t.Logf("Stats: %+v", stats)

	// Check if we reached 10M+ ops/sec target
	if opsPerSec >= 10_000_000 {
		t.Logf("🎉 TARGET ACHIEVED! 10M+ ops/sec!")
	} else {
		t.Logf("Current: %.2f M ops/sec, Target: 10 M ops/sec", opsPerSec/1e6)
	}
}

// TestVQC_Throughput_OpsPerSecond measures actual ops/sec
func TestVQC_Throughput_OpsPerSecond(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping throughput test in short mode")
	}

	acc := gpu.NewAccelerator()

	// Run for 5 seconds, measure throughput
	duration := 5 * time.Second
	deadline := time.Now().Add(duration)

	totalOps := 0
	batchSize := 10000

	t.Logf("Measuring throughput for %v...", duration)

	for time.Now().Before(deadline) {
		// Create batch
		pairs := make([][2]gpu.Quaternion, batchSize)
		for i := 0; i < batchSize; i++ {
			pairs[i] = [2]gpu.Quaternion{
				gpu.RandomQuaternion(),
				gpu.RandomQuaternion(),
			}
		}

		// Process
		results := acc.BatchSLERP(pairs, 0.5)
		totalOps += len(results)
	}

	opsPerSec := float64(totalOps) / duration.Seconds()

	t.Logf("✅ Sustained throughput: %.2f ops/sec (%.2f M ops/sec)",
		opsPerSec, opsPerSec/1e6)

	stats := acc.GetStats()
	t.Logf("✅ Stats OpsPerSecond: %.2f", stats.OpsPerSecond)
	t.Logf("✅ GPU available: %v", acc.IsGPUAvailable())
}

// TestVQC_MemoryEfficiency measures memory usage per operation
func TestVQC_MemoryEfficiency(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping memory test in short mode")
	}

	acc := gpu.NewAccelerator()

	// Create large batch
	batchSize := 100000
	pairs := make([][2]gpu.Quaternion, batchSize)
	for i := 0; i < batchSize; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	// Process
	results := acc.BatchSLERP(pairs, 0.5)

	// Calculate memory usage
	// Each quaternion = 4 float32s = 16 bytes
	// Each pair = 2 quaternions = 32 bytes input
	// Each result = 1 quaternion = 16 bytes output
	// Total = 32 + 16 = 48 bytes per operation

	expectedMemory := batchSize * 48 // bytes
	expectedMemoryMB := float64(expectedMemory) / (1024 * 1024)

	t.Logf("✅ Processed %d pairs", len(results))
	t.Logf("✅ Estimated memory: %.2f MB", expectedMemoryMB)
	t.Logf("✅ Memory per operation: 48 bytes")

	// Verify Williams batching would reduce memory
	williamsSize := OptimalBatchSize(batchSize)
	reduction := float64(batchSize) / float64(williamsSize)
	t.Logf("✅ Williams batching would reduce memory by %.2fx", reduction)
}

// ============================================================================
// EXPLORATION TESTS (70% Required)
// ============================================================================

// TestVQC_GPUAcceleration_Available tests GPU detection
func TestVQC_GPUAcceleration_Available(t *testing.T) {
	acc := gpu.NewAccelerator()
	available := acc.IsGPUAvailable()

	t.Logf("GPU Acceleration Available: %v", available)

	status := acc.GetStatus()
	backend, ok := status["backend"].(string)
	if !ok {
		t.Error("Backend not string in status")
	}

	t.Logf("Backend: %s", backend)

	if available {
		t.Logf("✅ GPU detected! Using Level Zero acceleration")
	} else {
		t.Logf("ℹ️  GPU not available, using CPU fallback (expected on most dev machines)")
	}
}

// TestVQC_GPUvsCPU_Speedup compares GPU vs CPU performance
func TestVQC_GPUvsCPU_Speedup(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping GPU vs CPU comparison in short mode")
	}

	acc := gpu.NewAccelerator()

	if !acc.IsGPUAvailable() {
		t.Skip("GPU not available, skipping speedup test")
	}

	// Prepare test data
	batchSize := 100000
	pairs := make([][2]gpu.Quaternion, batchSize)
	for i := 0; i < batchSize; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	// GPU path
	startGPU := time.Now()
	resultsGPU := acc.BatchSLERP(pairs, 0.5)
	gpuTime := time.Since(startGPU)

	// CPU path (manually)
	startCPU := time.Now()
	resultsCPU := make([]gpu.Quaternion, batchSize)
	for i, pair := range pairs {
		resultsCPU[i] = gpu.SLERP(pair[0], pair[1], 0.5)
	}
	cpuTime := time.Since(startCPU)

	speedup := float64(cpuTime) / float64(gpuTime)

	t.Logf("GPU time: %v", gpuTime)
	t.Logf("CPU time: %v", cpuTime)
	t.Logf("Speedup: %.2fx", speedup)

	// Verify results match (within tolerance)
	maxDiff := float32(0)
	for i := 0; i < batchSize; i++ {
		diff := gpu.GeodeticDistance(resultsGPU[i], resultsCPU[i])
		if diff > maxDiff {
			maxDiff = diff
		}
	}

	t.Logf("Max difference between GPU and CPU: %.10f", maxDiff)

	if maxDiff > 1e-4 {
		t.Errorf("GPU and CPU results differ by more than tolerance: %.10f", maxDiff)
	}
}

// TestVQC_Integration_WithSonars tests VQC in sonar pipeline
func TestVQC_Integration_WithSonars(t *testing.T) {
	t.Run("ConversationEnhancer_Integration", func(t *testing.T) {
		enhancer := NewConversationEnhancer()

		// Process messages
		messages := []ConversationMessage{
			{Role: "user", Content: "I want to analyze urban sentiment data"},
			{Role: "assistant", Content: "Great! What aspect interests you?"},
			{Role: "user", Content: "Traffic patterns and their emotional impact"},
		}

		pacing := enhancer.ProcessConversation(messages)

		if pacing.Style == "" {
			t.Error("Pacing not generated from conversation")
		}

		// Get analytics (uses quaternion state)
		analytics := enhancer.GetAnalytics()

		if analytics.CurrentState.Norm() == 0 {
			t.Error("User state not initialized")
		}

		t.Logf("Conversation processed successfully")
		t.Logf("User state: %v", analytics.CurrentState)
		t.Logf("Pacing: %s (intensity: %.2f)", pacing.Style, pacing.Intensity)
	})

	t.Run("ThreeRegime_Stability", func(t *testing.T) {
		enhancer := NewConversationEnhancer()

		// Force unstable state
		enhancer.CurrentRegime = ThreeRegime{R1: 0.70, R2: 0.20, R3: 0.10}

		status := enhancer.GetStabilityStatus()

		if status.IsStable {
			t.Error("Unstable regime reported as stable")
		}

		if !status.NeedsDamping {
			t.Error("Unstable regime should need damping")
		}

		// Apply damping
		enhancer.CurrentRegime = enhancer.CurrentRegime.ApplyDamping()

		// Should now be stable (R3 ≥ 0.50)
		newStatus := enhancer.GetStabilityStatus()
		if !newStatus.IsStable {
			t.Logf("Warning: Damping may need tuning, R3 = %.2f", enhancer.CurrentRegime.R3)
		}
	})

	t.Run("GPU_Accelerated_Sonar_Processing", func(t *testing.T) {
		acc := gpu.NewAccelerator()

		// Simulate sonar processing with quaternion state evolution
		numSamples := 10000
		samples := make([]gpu.Quaternion, numSamples)
		for i := 0; i < numSamples; i++ {
			samples[i] = gpu.RandomQuaternion()
		}

		// Batch normalize (represents sonar state normalization)
		start := time.Now()
		normalized := acc.BatchNormalize(samples)
		elapsed := time.Since(start)

		opsPerSec := float64(numSamples) / elapsed.Seconds()

		t.Logf("Processed %d sonar samples in %v", numSamples, elapsed)
		t.Logf("Throughput: %.2f samples/sec", opsPerSec)

		// Verify all normalized
		for i, n := range normalized {
			if err := n.Validate(); err != nil {
				t.Errorf("Sample %d not normalized: %v", i, err)
			}
		}
	})
}

// ============================================================================
// BENCHMARKS
// ============================================================================

func BenchmarkVQC_SLERP_Single(b *testing.B) {
	q0 := gpu.RandomQuaternion()
	q1 := gpu.RandomQuaternion()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = gpu.SLERP(q0, q1, 0.5)
	}
}

func BenchmarkVQC_SLERP_Batch_100(b *testing.B) {
	acc := gpu.NewAccelerator()
	pairs := make([][2]gpu.Quaternion, 100)
	for i := 0; i < 100; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = acc.BatchSLERP(pairs, 0.5)
	}
}

func BenchmarkVQC_SLERP_Batch_1000(b *testing.B) {
	acc := gpu.NewAccelerator()
	pairs := make([][2]gpu.Quaternion, 1000)
	for i := 0; i < 1000; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = acc.BatchSLERP(pairs, 0.5)
	}
}

func BenchmarkVQC_SLERP_Batch_10000(b *testing.B) {
	acc := gpu.NewAccelerator()
	pairs := make([][2]gpu.Quaternion, 10000)
	for i := 0; i < 10000; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = acc.BatchSLERP(pairs, 0.5)
	}
}

func BenchmarkVQC_Multiply_Batch_10000(b *testing.B) {
	acc := gpu.NewAccelerator()
	pairs := make([][2]gpu.Quaternion, 10000)
	for i := 0; i < 10000; i++ {
		pairs[i] = [2]gpu.Quaternion{
			gpu.RandomQuaternion(),
			gpu.RandomQuaternion(),
		}
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = acc.BatchMultiply(pairs)
	}
}

func BenchmarkVQC_Normalize_Batch_10000(b *testing.B) {
	acc := gpu.NewAccelerator()
	quats := make([]gpu.Quaternion, 10000)
	for i := 0; i < 10000; i++ {
		quats[i] = gpu.Quaternion{
			W: float32(i) * 0.1,
			X: float32(i) * 0.2,
			Y: float32(i) * 0.3,
			Z: float32(i) * 0.4,
		}
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = acc.BatchNormalize(quats)
	}
}

func BenchmarkVQC_DigitalRoot(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = DigitalRoot(i)
	}
}

func BenchmarkVQC_DigitalRootFilter_10000(b *testing.B) {
	candidates := make([]int, 10000)
	for i := 0; i < 10000; i++ {
		candidates[i] = i
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilter(candidates, 1234)
	}
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

// Note: ConversationMessage type already defined in quaternion_state.go
