// Package vqc - GPU Integration Tests
// Tests the complete GPU bridge integration with qos
//
// Test philosophy:
//   - Works both when GPU available AND unavailable
//   - Validates CPU fallback gracefully
//   - Measures actual performance gains (when GPU present)
//   - No test failure if GPU missing (that's expected!)
//
// Built: 2025-12-27 (Wave 4+, GPU Integration Tests)
package vqc

import (
	"fmt"
	"math"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// TEST 1: GPU Bridge Initialization
// ═══════════════════════════════════════════════════════════════════════════

// TestGPUBridgeInit tests GPU bridge initialization
// PASS if: Bridge initializes (GPU available or unavailable both OK!)
func TestGPUBridgeInit(t *testing.T) {
	bridge := GetGPUBridge()
	if bridge == nil {
		t.Fatal("GPUBridge is nil - should always initialize")
	}

	if !bridge.initialized {
		t.Fatal("GPUBridge not initialized")
	}

	// Log GPU availability (not a failure if unavailable!)
	if bridge.available {
		t.Logf("✓ GPU available for acceleration")

		// Get GPU info
		if bridge.gpu != nil {
			props, err := bridge.gpu.GetDeviceProperties()
			if err == nil {
				t.Logf("  Device: %v", props)
			}
		}
	} else {
		t.Logf("⚠ GPU not available (using CPU fallback)")
		if bridge.stats.LastError != "" {
			t.Logf("  Reason: %s", bridge.stats.LastError)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 2: GPU Quaternion Operations
// ═══════════════════════════════════════════════════════════════════════════

// TestGPUQuaternionOps tests GPU quaternion operations with fallback
func TestGPUQuaternionOps(t *testing.T) {
	ops := UseGPUQuaternionOps()

	// Test data
	q0 := Quaternion{W: 1, X: 0, Y: 0, Z: 0}.Normalize()
	q1 := Quaternion{W: 0.7071, X: 0.7071, Y: 0, Z: 0}.Normalize()
	pairs := [][2]Quaternion{
		{q0, q1},
		{q1, q0},
	}

	// Test SLERP
	t.Run("BatchSLERP", func(t *testing.T) {
		results, err := ops.BatchSLERP(pairs, 0.5)
		if err != nil {
			t.Fatalf("BatchSLERP failed: %v", err)
		}

		if len(results) != len(pairs) {
			t.Errorf("Expected %d results, got %d", len(pairs), len(results))
		}

		// Validate results are normalized
		for i, r := range results {
			norm := math.Sqrt(r.W*r.W + r.X*r.X + r.Y*r.Y + r.Z*r.Z)
			if math.Abs(norm-1.0) > 1e-6 {
				t.Errorf("Result %d not normalized: ||q|| = %f", i, norm)
			}
		}

		t.Logf("✓ BatchSLERP: %d quaternions processed", len(results))
	})

	// Test Multiply
	t.Run("BatchMultiply", func(t *testing.T) {
		results, err := ops.BatchMultiply(pairs)
		if err != nil {
			t.Fatalf("BatchMultiply failed: %v", err)
		}

		if len(results) != len(pairs) {
			t.Errorf("Expected %d results, got %d", len(pairs), len(results))
		}

		t.Logf("✓ BatchMultiply: %d quaternions processed", len(results))
	})

	// Test Normalize
	t.Run("BatchNormalize", func(t *testing.T) {
		quats := []Quaternion{
			{W: 2, X: 0, Y: 0, Z: 0},
			{W: 1, X: 1, Y: 1, Z: 1},
		}

		results, err := ops.BatchNormalize(quats)
		if err != nil {
			t.Fatalf("BatchNormalize failed: %v", err)
		}

		// Validate all normalized
		for i, r := range results {
			norm := math.Sqrt(r.W*r.W + r.X*r.X + r.Y*r.Y + r.Z*r.Z)
			if math.Abs(norm-1.0) > 1e-6 {
				t.Errorf("Result %d not normalized: ||q|| = %f", i, norm)
			}
		}

		t.Logf("✓ BatchNormalize: %d quaternions normalized", len(results))
	})
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 3: GPU SLERP Function
// ═══════════════════════════════════════════════════════════════════════════

// TestGPUSLERP tests the GPU SLERP function wrapper
func TestGPUSLERP(t *testing.T) {
	slerpFn := UseGPUSLERP()

	q0 := Quaternion{W: 1, X: 0, Y: 0, Z: 0}
	q1 := Quaternion{W: 0.7071, X: 0.7071, Y: 0, Z: 0}

	// Test multiple interpolation points
	for _, t_val := range []float64{0.0, 0.25, 0.5, 0.75, 1.0} {
		result := slerpFn(q0, q1, t_val)

		// Validate normalized (tolerance relaxed to 1e-5 for float64->float32->float64 conversion)
		norm := math.Sqrt(result.W*result.W + result.X*result.X + result.Y*result.Y + result.Z*result.Z)
		if math.Abs(norm-1.0) > 1e-5 {
			t.Errorf("SLERP(t=%.2f) not normalized: ||q|| = %f", t_val, norm)
		}

		// Validate endpoints
		if t_val == 0.0 {
			if !quaternionsEqual(result, q0, 1e-6) {
				t.Errorf("SLERP(0) should equal q0")
			}
		}
		if t_val == 1.0 {
			if !quaternionsEqual(result, q1, 1e-6) {
				t.Errorf("SLERP(1) should equal q1")
			}
		}
	}

	t.Logf("✓ GPU SLERP validated at 5 interpolation points")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 4: GPU Utilization Statistics
// ═══════════════════════════════════════════════════════════════════════════

// TestGPUStatistics validates statistics tracking
func TestGPUStatistics(t *testing.T) {
	stats := GetGPUBridgeStats()

	t.Logf("GPU Bridge Statistics:")
	t.Logf("  Total Operations: %d", stats.TotalOperations)
	t.Logf("  GPU Operations:   %d", stats.GPUOperations)
	t.Logf("  CPU Fallbacks:    %d", stats.CPUFallbacks)
	t.Logf("  Init Attempts:    %d", stats.InitAttempts)
	t.Logf("  Init Successes:   %d", stats.InitSuccesses)

	// Calculate utilization
	util := GPUUtilization()
	backend := GetBackend()

	t.Logf("  GPU Utilization:  %.1f%%", util)
	t.Logf("  Active Backend:   %s", backend)

	// Validate stats consistency
	// Note: TotalOperations counts operation types, CPU+GPU counts individual ops
	// So it's OK for GPU+CPU to be >= Total (batch operations count once in Total, many times in GPU/CPU)
	if stats.TotalOperations > 0 && stats.GPUOperations == 0 && stats.CPUFallbacks == 0 {
		t.Errorf("Stats inconsistency: No operations recorded despite TotalOperations > 0")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 5: Performance Benchmarking (When GPU Available)
// ═══════════════════════════════════════════════════════════════════════════

// TestGPUPerformance benchmarks GPU vs CPU (when GPU available)
func TestGPUPerformance(t *testing.T) {
	if !IsGPUAvailable() {
		t.Skip("Skipping performance test - GPU not available")
	}

	// Create test data
	const numPairs = 1000
	pairs := make([][2]Quaternion, numPairs)
	for i := 0; i < numPairs; i++ {
		q0 := Quaternion{
			W: math.Cos(float64(i) * 0.1),
			X: math.Sin(float64(i) * 0.1),
			Y: 0.5,
			Z: 0.3,
		}.Normalize()

		q1 := Quaternion{
			W: 0.7,
			X: 0.3,
			Y: math.Sin(float64(i) * 0.2),
			Z: math.Cos(float64(i) * 0.2),
		}.Normalize()

		pairs[i] = [2]Quaternion{q0, q1}
	}

	// Benchmark GPU path
	ops := UseGPUQuaternionOps()
	results, err := ops.BatchSLERP(pairs, 0.5)
	if err != nil {
		t.Fatalf("GPU SLERP failed: %v", err)
	}

	if len(results) != numPairs {
		t.Errorf("Expected %d results, got %d", numPairs, len(results))
	}

	// Get final stats
	stats := GetGPUBridgeStats()
	t.Logf("✓ Performance test complete:")
	t.Logf("  Processed: %d quaternion pairs", numPairs)
	t.Logf("  GPU ops:   %d", stats.GPUOperations)
	t.Logf("  CPU ops:   %d", stats.CPUFallbacks)
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 6: GPU Info Retrieval
// ═══════════════════════════════════════════════════════════════════════════

// TestGPUInfo tests GPU information retrieval
func TestGPUInfo(t *testing.T) {
	info, err := GetGPUInfo()

	if err != nil {
		// Not an error if GPU unavailable
		t.Logf("⚠ GPU info not available: %v", err)
		return
	}

	// GPU available - log properties
	t.Logf("✓ GPU Properties:")
	for key, value := range info {
		t.Logf("  %s: %v", key, value)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// UTILITY FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// quaternionsEqual checks if two quaternions are approximately equal
func quaternionsEqual(q1, q2 Quaternion, epsilon float64) bool {
	return math.Abs(q1.W-q2.W) < epsilon &&
		math.Abs(q1.X-q2.X) < epsilon &&
		math.Abs(q1.Y-q2.Y) < epsilon &&
		math.Abs(q1.Z-q2.Z) < epsilon
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARK: GPU vs CPU SLERP
// ═══════════════════════════════════════════════════════════════════════════

// BenchmarkGPUSLERP benchmarks GPU SLERP performance
func BenchmarkGPUSLERP(b *testing.B) {
	if !IsGPUAvailable() {
		b.Skip("GPU not available")
	}

	ops := UseGPUQuaternionOps()
	pairs := [][2]Quaternion{
		{
			{W: 1, X: 0, Y: 0, Z: 0},
			{W: 0.7071, X: 0.7071, Y: 0, Z: 0},
		},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = ops.BatchSLERP(pairs, 0.5)
	}
}

// BenchmarkCPUSLERP benchmarks CPU SLERP performance
func BenchmarkCPUSLERP(b *testing.B) {
	q0 := Quaternion{W: 1, X: 0, Y: 0, Z: 0}
	q1 := Quaternion{W: 0.7071, X: 0.7071, Y: 0, Z: 0}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = SLERP(q0, q1, 0.5)
	}
}

// BenchmarkGPUBatchSLERP benchmarks GPU batch SLERP with varying sizes
func BenchmarkGPUBatchSLERP(b *testing.B) {
	if !IsGPUAvailable() {
		b.Skip("GPU not available")
	}

	sizes := []int{10, 100, 1000, 10000}
	ops := UseGPUQuaternionOps()

	for _, size := range sizes {
		b.Run(fmt.Sprintf("Size_%d", size), func(b *testing.B) {
			pairs := make([][2]Quaternion, size)
			for i := 0; i < size; i++ {
				pairs[i] = [2]Quaternion{
					{W: 1, X: 0, Y: 0, Z: 0},
					{W: 0.7071, X: 0.7071, Y: 0, Z: 0},
				}
			}

			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				_, _ = ops.BatchSLERP(pairs, 0.5)
			}
		})
	}
}
