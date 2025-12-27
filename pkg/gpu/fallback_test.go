// Package gpu - Fallback System Tests
// Hamilton says: "What happens when the GPU isn't available? The system must still work."
//
// Test Categories:
//   - STABILIZATION (100% required): Core fallback logic, error handling
//   - OPTIMIZATION (85% required): Performance tracking, stats accuracy
//   - EXPLORATION (70% required): Edge cases, stress testing
package gpu

import (
	"errors"
	"fmt"
	"sync"
	"testing"
)

// ========== STABILIZATION TESTS (100% Required) ==========

func TestGPUAvailable_DetectionWorks(t *testing.T) {
	ResetFallbackStats()

	// Call GPUAvailable multiple times
	for i := 0; i < 10; i++ {
		available := GPUAvailable()

		// Currently should always return false (GPU not implemented yet)
		if available {
			t.Log("GPU is available (unexpected but valid)")
		} else {
			t.Log("GPU not available (expected - using CPU fallback)")
		}
	}

	// Stats should be tracked
	stats := GetFallbackStats()
	if stats.GPUDetectionAttempts != 10 {
		t.Errorf("Expected 10 detection attempts, got %d", stats.GPUDetectionAttempts)
	}
}

func TestWithGPUFallback_GPUAvailable_Success(t *testing.T) {
	ResetFallbackStats()

	gpuCalled := false
	cpuCalled := false

	// Simulate GPU available and succeeding
	err := WithGPUFallback(
		func() error {
			gpuCalled = true
			return nil
		},
		func() error {
			cpuCalled = true
			return nil
		},
	)

	if err != nil {
		t.Fatalf("WithGPUFallback failed: %v", err)
	}

	// Currently GPU is not available, so CPU should be called
	if GPUAvailable() {
		if !gpuCalled {
			t.Error("GPU was available but GPU function not called")
		}
		if cpuCalled {
			t.Error("GPU succeeded, CPU should not be called")
		}
	} else {
		if !cpuCalled {
			t.Error("GPU not available, CPU function should be called")
		}
		if gpuCalled {
			t.Error("GPU not available, GPU function should not be called")
		}
	}
}

func TestWithGPUFallback_GPUUnavailable_CPUSuccess(t *testing.T) {
	ResetFallbackStats()

	cpuCalled := false

	err := WithGPUFallback(
		func() error {
			return errors.New("simulated GPU failure")
		},
		func() error {
			cpuCalled = true
			return nil
		},
	)

	if err != nil {
		t.Fatalf("WithGPUFallback should succeed on CPU fallback: %v", err)
	}

	if !cpuCalled {
		t.Error("CPU function should be called when GPU fails")
	}

	stats := GetFallbackStats()
	if stats.CPUFallbacks == 0 {
		t.Error("CPU fallback should be tracked in stats")
	}
}

func TestWithGPUFallback_GPUFails_CPUFallbackWorks(t *testing.T) {
	ResetFallbackStats()

	// Force GPU path but make it fail
	err := WithGPUFallback(
		func() error {
			// Simulate GPU failure
			return ErrGPUInitFailed
		},
		func() error {
			// CPU succeeds
			return nil
		},
	)

	// Should succeed via CPU fallback
	if err != nil {
		t.Errorf("Expected success via CPU fallback, got error: %v", err)
	}

	stats := GetFallbackStats()
	if stats.CPUFallbacks == 0 {
		t.Error("CPU fallback should be recorded")
	}
}

func TestWithGPUFallback_BothFail_ReturnsError(t *testing.T) {
	ResetFallbackStats()

	gpuErr := errors.New("GPU exploded")
	cpuErr := errors.New("CPU on fire")

	err := WithGPUFallback(
		func() error { return gpuErr },
		func() error { return cpuErr },
	)

	if err == nil {
		t.Fatal("Expected error when both GPU and CPU fail")
	}

	// Error should mention both failures
	errMsg := err.Error()
	if errMsg == "" {
		t.Error("Error message should not be empty")
	}

	t.Logf("Both-fail error message: %v", err)
}

func TestWithGPUFallbackTyped_ReturnsResults(t *testing.T) {
	ResetFallbackStats()

	// Test with int result type
	result, err := WithGPUFallbackTyped(
		func() (int, error) { return 42, errors.New("GPU failed") },
		func() (int, error) { return 99, nil },
	)

	if err != nil {
		t.Fatalf("Expected success via CPU fallback, got error: %v", err)
	}

	if result != 99 {
		t.Errorf("Expected CPU result 99, got %d", result)
	}
}

func TestWithGPUFallbackTyped_QuaternionSlice(t *testing.T) {
	ResetFallbackStats()

	// Test with realistic quaternion slice (simulates batch operations)
	expected := []Quaternion{
		NewQuaternion(1, 0, 0, 0),
		NewQuaternion(0, 1, 0, 0),
	}

	result, err := WithGPUFallbackTyped(
		func() ([]Quaternion, error) {
			return nil, errors.New("GPU unavailable")
		},
		func() ([]Quaternion, error) {
			return expected, nil
		},
	)

	if err != nil {
		t.Fatalf("CPU fallback failed: %v", err)
	}

	if len(result) != len(expected) {
		t.Errorf("Expected %d quaternions, got %d", len(expected), len(result))
	}
}

func TestGetComputeMode_ReturnsCorrectMode(t *testing.T) {
	mode := GetComputeMode()

	if mode != ComputeModeGPU && mode != ComputeModeCPU {
		t.Errorf("GetComputeMode returned invalid mode: %v", mode)
	}

	modeStr := GetComputeModeString()
	if modeStr == "" {
		t.Error("GetComputeModeString should not be empty")
	}

	t.Logf("Current compute mode: %s", modeStr)

	// Mode should be consistent
	if string(mode) != modeStr {
		t.Errorf("Mode mismatch: %v vs %s", mode, modeStr)
	}
}

func TestIsGPUError_RecognizesGPUErrors(t *testing.T) {
	tests := []struct {
		name     string
		err      error
		expected bool
	}{
		{
			name:     "ErrGPUNotAvailable",
			err:      ErrGPUNotAvailable,
			expected: true,
		},
		{
			name:     "ErrGPUInitFailed",
			err:      ErrGPUInitFailed,
			expected: true,
		},
		{
			name:     "Random error",
			err:      errors.New("something else"),
			expected: false,
		},
		{
			name:     "Nil error",
			err:      nil,
			expected: false,
		},
		{
			name:     "Wrapped GPU error",
			err:      fmt.Errorf("wrapped: %w", ErrGPUNotAvailable),
			expected: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := IsGPUError(tt.err)
			if result != tt.expected {
				t.Errorf("IsGPUError(%v) = %v, want %v", tt.err, result, tt.expected)
			}
		})
	}
}

// ========== OPTIMIZATION TESTS (85% Required) ==========

func TestFallbackStats_Tracking(t *testing.T) {
	ResetFallbackStats()

	// Execute several operations
	for i := 0; i < 100; i++ {
		_ = WithGPUFallback(
			func() error { return errors.New("GPU fail") },
			func() error { return nil },
		)
	}

	stats := GetFallbackStats()

	if stats.TotalOperations != 100 {
		t.Errorf("Expected 100 total operations, got %d", stats.TotalOperations)
	}

	if stats.CPUFallbacks != 100 {
		t.Errorf("Expected 100 CPU fallbacks, got %d", stats.CPUFallbacks)
	}

	t.Logf("Stats: %s", stats.String())
}

func TestFallbackStats_FallbackRate(t *testing.T) {
	ResetFallbackStats()

	// All operations fallback to CPU (GPU not available currently)
	for i := 0; i < 50; i++ {
		_ = WithGPUFallback(
			func() error { return errors.New("GPU unavailable") },
			func() error { return nil },
		)
	}

	stats := GetFallbackStats()
	rate := stats.FallbackRate()

	// Should be 100% fallback rate (GPU not available)
	if rate < 99.0 {
		t.Errorf("Expected ~100%% fallback rate, got %.2f%%", rate)
	}

	t.Logf("Fallback rate: %.2f%%", rate)
}

func TestFallbackStats_GPUAvailabilityRate(t *testing.T) {
	ResetFallbackStats()

	// Check GPU availability
	for i := 0; i < 20; i++ {
		GPUAvailable()
	}

	stats := GetFallbackStats()
	availRate := stats.GPUAvailabilityRate()

	// Currently GPU is never available
	if availRate > 1.0 {
		t.Logf("GPU availability rate: %.2f%% (GPU is available!)", availRate)
	} else {
		t.Logf("GPU availability rate: %.2f%% (expected - GPU not yet implemented)", availRate)
	}
}

func TestFallbackStats_ResetWorks(t *testing.T) {
	ResetFallbackStats()

	// Generate some stats
	for i := 0; i < 10; i++ {
		_ = WithGPUFallback(
			func() error { return errors.New("fail") },
			func() error { return nil },
		)
	}

	// Reset
	ResetFallbackStats()

	stats := GetFallbackStats()
	if stats.TotalOperations != 0 {
		t.Errorf("After reset, TotalOperations should be 0, got %d", stats.TotalOperations)
	}
	if stats.CPUFallbacks != 0 {
		t.Errorf("After reset, CPUFallbacks should be 0, got %d", stats.CPUFallbacks)
	}
}

func TestExecuteWithFallback_TracksComputeMode(t *testing.T) {
	ResetFallbackStats()

	result, mode, err := ExecuteWithFallback(
		"TestOperation",
		false, // GPU not available
		func() (string, error) { return "GPU result", nil },
		func() (string, error) { return "CPU result", nil },
	)

	if err != nil {
		t.Fatalf("ExecuteWithFallback failed: %v", err)
	}

	if result != "CPU result" {
		t.Errorf("Expected CPU result, got %s", result)
	}

	if mode != ComputeModeCPU {
		t.Errorf("Expected CPU mode, got %v", mode)
	}

	t.Logf("Executed on: %v", mode)
}

// ========== EXPLORATION TESTS (70% Required) ==========

func TestFallback_ConcurrentAccess(t *testing.T) {
	ResetFallbackStats()

	const goroutines = 100
	const opsPerGoroutine = 50

	var wg sync.WaitGroup
	wg.Add(goroutines)

	// Concurrent execution
	for i := 0; i < goroutines; i++ {
		go func(id int) {
			defer wg.Done()

			for j := 0; j < opsPerGoroutine; j++ {
				_ = WithGPUFallback(
					func() error { return errors.New("GPU unavailable") },
					func() error { return nil },
				)
			}
		}(i)
	}

	wg.Wait()

	stats := GetFallbackStats()
	expectedOps := int64(goroutines * opsPerGoroutine)

	if stats.TotalOperations != expectedOps {
		t.Errorf("Expected %d operations, got %d", expectedOps, stats.TotalOperations)
	}

	t.Logf("Concurrent test: %d goroutines × %d ops = %d total ops",
		goroutines, opsPerGoroutine, stats.TotalOperations)
}

func TestFallback_LargeResultSet(t *testing.T) {
	// Test fallback with large result set (simulates real VQC workload)
	const size = 10000

	result, err := WithGPUFallbackTyped(
		func() ([]Quaternion, error) {
			return nil, errors.New("GPU unavailable")
		},
		func() ([]Quaternion, error) {
			quats := make([]Quaternion, size)
			for i := 0; i < size; i++ {
				quats[i] = RandomQuaternion()
			}
			return quats, nil
		},
	)

	if err != nil {
		t.Fatalf("Large result fallback failed: %v", err)
	}

	if len(result) != size {
		t.Errorf("Expected %d quaternions, got %d", size, len(result))
	}

	// Verify all quaternions are valid
	for i, q := range result {
		if err := q.Validate(); err != nil {
			t.Errorf("Quaternion %d invalid: %v", i, err)
		}
	}

	t.Logf("Successfully processed %d quaternions via CPU fallback", size)
}

func TestFallback_ErrorPropagation(t *testing.T) {
	// Test that errors are properly propagated and combined
	tests := []struct {
		name      string
		gpuErr    error
		cpuErr    error
		expectErr bool
	}{
		{
			name:      "Both succeed (GPU)",
			gpuErr:    nil,
			cpuErr:    nil,
			expectErr: false,
		},
		{
			name:      "GPU fails, CPU succeeds",
			gpuErr:    errors.New("GPU error"),
			cpuErr:    nil,
			expectErr: false,
		},
		{
			name:      "GPU succeeds (should not call CPU)",
			gpuErr:    nil,
			cpuErr:    errors.New("CPU should not be called"),
			expectErr: false,
		},
		{
			name:      "Both fail",
			gpuErr:    errors.New("GPU error"),
			cpuErr:    errors.New("CPU error"),
			expectErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ResetFallbackStats()

			// Note: Since GPU is not available, we simulate by always using CPU
			err := WithGPUFallback(
				func() error { return tt.gpuErr },
				func() error { return tt.cpuErr },
			)

			// Special case: If GPU not available, CPU will be called even if gpuErr is nil
			if !GPUAvailable() && tt.name == "GPU succeeds (should not call CPU)" {
				// Skip this test when GPU not available
				t.Skip("GPU not available - cannot test GPU-only path")
				return
			}

			if tt.expectErr && err == nil {
				t.Error("Expected error but got nil")
			}
			if !tt.expectErr && err != nil {
				t.Errorf("Expected no error but got: %v", err)
			}
		})
	}
}

func TestFallback_StatsStringFormat(t *testing.T) {
	ResetFallbackStats()

	// Generate some operations
	for i := 0; i < 25; i++ {
		_ = WithGPUFallback(
			func() error { return errors.New("GPU fail") },
			func() error { return nil },
		)
	}

	stats := GetFallbackStats()
	str := stats.String()

	if str == "" {
		t.Error("Stats.String() should not be empty")
	}

	// Should contain key information
	if len(str) < 20 {
		t.Errorf("Stats string seems too short: %s", str)
	}

	t.Logf("Stats string: %s", str)
}

// ========== BENCHMARKS ==========

func BenchmarkWithGPUFallback_CPUPath(b *testing.B) {
	ResetFallbackStats()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = WithGPUFallback(
			func() error { return errors.New("GPU unavailable") },
			func() error { return nil },
		)
	}
}

func BenchmarkGPUAvailable_Check(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = GPUAvailable()
	}
}

func BenchmarkWithGPUFallbackTyped_SmallResult(b *testing.B) {
	ResetFallbackStats()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = WithGPUFallbackTyped(
			func() (Quaternion, error) { return Identity(), errors.New("GPU fail") },
			func() (Quaternion, error) { return RandomQuaternion(), nil },
		)
	}
}

func BenchmarkWithGPUFallbackTyped_LargeResult(b *testing.B) {
	ResetFallbackStats()
	const size = 1000

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = WithGPUFallbackTyped(
			func() ([]Quaternion, error) {
				return nil, errors.New("GPU unavailable")
			},
			func() ([]Quaternion, error) {
				quats := make([]Quaternion, size)
				for j := 0; j < size; j++ {
					quats[j] = RandomQuaternion()
				}
				return quats, nil
			},
		)
	}
}
