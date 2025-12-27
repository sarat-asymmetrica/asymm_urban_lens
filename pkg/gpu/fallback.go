// Package gpu - Graceful GPU → CPU Fallback Infrastructure
// Hamilton says: "What happens when the GPU isn't available? The system must still work."
//
// Philosophy:
//   - GPU unavailable = NOT a failure, just a different execution path
//   - Graceful degradation > Hard failures
//   - Observability > Silent fallbacks (log warnings, track stats)
//   - User should never see GPU errors, only see it working
//
// Built: 2025-12-27 (Wave 4, Agent 2)
// Foundation: Asymmetrica Mathematical Organism reliability standards
package gpu

import (
	"errors"
	"fmt"
	"log"
	"sync"
	"sync/atomic"

	"github.com/asymmetrica/urbanlens/pkg/qos"
)

// ═══════════════════════════════════════════════════════════════════════════
// FALLBACK STATISTICS
// ═══════════════════════════════════════════════════════════════════════════

// FallbackStats tracks GPU availability and fallback behavior
type FallbackStats struct {
	GPUDetectionAttempts int64 // How many times we checked for GPU
	GPUSuccesses         int64 // How many times GPU was available
	GPUFailures          int64 // How many times GPU failed
	CPUFallbacks         int64 // How many times we fell back to CPU
	TotalOperations      int64 // Total operations executed
}

var globalFallbackStats FallbackStats

// ═══════════════════════════════════════════════════════════════════════════
// GPU AVAILABILITY CHECK
// ═══════════════════════════════════════════════════════════════════════════

// GPUAvailable checks if GPU acceleration is currently available
// Returns: true if GPU can be used, false if must use CPU fallback
//
// Implementation notes:
//   - Currently returns false (GPU detection not yet implemented)
//   - Future: Will check Level Zero GPU availability
//   - Caches result to avoid repeated detection overhead
func GPUAvailable() bool {
	atomic.AddInt64(&globalFallbackStats.GPUDetectionAttempts, 1)

	available := detectGPU()

	if available {
		atomic.AddInt64(&globalFallbackStats.GPUSuccesses, 1)
	} else {
		atomic.AddInt64(&globalFallbackStats.GPUFailures, 1)
	}

	return available
}

// ═══════════════════════════════════════════════════════════════════════════
// FALLBACK EXECUTION WRAPPER
// ═══════════════════════════════════════════════════════════════════════════

// WithGPUFallback executes gpuFn if GPU available, otherwise executes cpuFn
// Logs warnings on GPU unavailability (not errors - this is expected behavior!)
//
// Example usage:
//   err := WithGPUFallback(
//       func() error { return processOnGPU(data) },
//       func() error { return processOnCPU(data) },
//   )
//
// Returns:
//   - nil if either path succeeds
//   - error if the executed path fails
func WithGPUFallback(gpuFn, cpuFn func() error) error {
	atomic.AddInt64(&globalFallbackStats.TotalOperations, 1)

	if GPUAvailable() {
		err := gpuFn()
		if err == nil {
			return nil
		}

		// GPU failed - log and fallback to CPU
		log.Printf("[GPU→CPU Fallback] GPU execution failed: %v. Falling back to CPU.", err)
		atomic.AddInt64(&globalFallbackStats.CPUFallbacks, 1)

		// Try CPU fallback
		cpuErr := cpuFn()
		if cpuErr != nil {
			return fmt.Errorf("GPU failed (%v), CPU fallback also failed (%v)", err, cpuErr)
		}
		return nil
	}

	// GPU not available - use CPU directly
	atomic.AddInt64(&globalFallbackStats.CPUFallbacks, 1)
	return cpuFn()
}

// WithGPUFallbackTyped executes GPU or CPU function and returns typed result
// Generic version for functions that return values
//
// Example:
//   result, err := WithGPUFallbackTyped(
//       func() ([]Quaternion, error) { return batchSLERPGPU(pairs, t) },
//       func() ([]Quaternion, error) { return batchSLERPCPU(pairs, t) },
//   )
func WithGPUFallbackTyped[T any](gpuFn, cpuFn func() (T, error)) (T, error) {
	atomic.AddInt64(&globalFallbackStats.TotalOperations, 1)
	var zero T

	if GPUAvailable() {
		result, err := gpuFn()
		if err == nil {
			return result, nil
		}

		// GPU failed - log and fallback
		log.Printf("[GPU→CPU Fallback] GPU execution failed: %v. Falling back to CPU.", err)
		atomic.AddInt64(&globalFallbackStats.CPUFallbacks, 1)

		cpuResult, cpuErr := cpuFn()
		if cpuErr != nil {
			return zero, fmt.Errorf("GPU failed (%v), CPU fallback also failed (%v)", err, cpuErr)
		}
		return cpuResult, nil
	}

	// GPU not available - use CPU directly
	atomic.AddInt64(&globalFallbackStats.CPUFallbacks, 1)
	return cpuFn()
}

// ═══════════════════════════════════════════════════════════════════════════
// COMPUTE MODE REPORTING
// ═══════════════════════════════════════════════════════════════════════════

// ComputeMode represents the execution backend being used
type ComputeMode string

const (
	ComputeModeGPU     ComputeMode = "GPU"     // Using GPU acceleration
	ComputeModeCPU     ComputeMode = "CPU"     // Using CPU fallback
	ComputeModeUnknown ComputeMode = "Unknown" // Status unknown
)

// GetComputeMode returns current compute mode based on GPU availability
func GetComputeMode() ComputeMode {
	if GPUAvailable() {
		return ComputeModeGPU
	}
	return ComputeModeCPU
}

// GetComputeModeString returns compute mode as string (for API responses)
func GetComputeModeString() string {
	return string(GetComputeMode())
}

// ═══════════════════════════════════════════════════════════════════════════
// STATISTICS & OBSERVABILITY
// ═══════════════════════════════════════════════════════════════════════════

// GetFallbackStats returns current fallback statistics
// Use this for monitoring and observability
func GetFallbackStats() FallbackStats {
	return FallbackStats{
		GPUDetectionAttempts: atomic.LoadInt64(&globalFallbackStats.GPUDetectionAttempts),
		GPUSuccesses:         atomic.LoadInt64(&globalFallbackStats.GPUSuccesses),
		GPUFailures:          atomic.LoadInt64(&globalFallbackStats.GPUFailures),
		CPUFallbacks:         atomic.LoadInt64(&globalFallbackStats.CPUFallbacks),
		TotalOperations:      atomic.LoadInt64(&globalFallbackStats.TotalOperations),
	}
}

// ResetFallbackStats resets statistics (for testing)
func ResetFallbackStats() {
	atomic.StoreInt64(&globalFallbackStats.GPUDetectionAttempts, 0)
	atomic.StoreInt64(&globalFallbackStats.GPUSuccesses, 0)
	atomic.StoreInt64(&globalFallbackStats.GPUFailures, 0)
	atomic.StoreInt64(&globalFallbackStats.CPUFallbacks, 0)
	atomic.StoreInt64(&globalFallbackStats.TotalOperations, 0)
}

// FallbackRate returns percentage of operations that used CPU fallback
func (s FallbackStats) FallbackRate() float64 {
	if s.TotalOperations == 0 {
		return 0.0
	}
	return float64(s.CPUFallbacks) / float64(s.TotalOperations) * 100.0
}

// GPUAvailabilityRate returns percentage of GPU detection successes
func (s FallbackStats) GPUAvailabilityRate() float64 {
	if s.GPUDetectionAttempts == 0 {
		return 0.0
	}
	return float64(s.GPUSuccesses) / float64(s.GPUDetectionAttempts) * 100.0
}

// String returns human-readable stats
func (s FallbackStats) String() string {
	return fmt.Sprintf(
		"FallbackStats{Ops: %d, GPU: %d, CPU: %d, FallbackRate: %.1f%%, GPUAvail: %.1f%%}",
		s.TotalOperations,
		s.TotalOperations-s.CPUFallbacks,
		s.CPUFallbacks,
		s.FallbackRate(),
		s.GPUAvailabilityRate(),
	)
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR TYPES
// ═══════════════════════════════════════════════════════════════════════════

var (
	// ErrGPUNotAvailable indicates GPU is not available (not a failure!)
	ErrGPUNotAvailable = errors.New("GPU not available (using CPU fallback)")

	// ErrGPUInitFailed indicates GPU initialization failed
	ErrGPUInitFailed = errors.New("GPU initialization failed")

	// ErrBothFailed indicates both GPU and CPU paths failed
	ErrBothFailed = errors.New("both GPU and CPU execution failed")
)

// IsGPUError checks if error is GPU-related (should trigger fallback)
func IsGPUError(err error) bool {
	return errors.Is(err, ErrGPUNotAvailable) || errors.Is(err, ErrGPUInitFailed)
}

// ═══════════════════════════════════════════════════════════════════════════
// INTEGRATION WITH ACCELERATOR
// ═══════════════════════════════════════════════════════════════════════════

// ExecuteWithFallback is a helper for Accelerator methods
// Automatically tracks stats and logs appropriately
func ExecuteWithFallback[T any](
	operationName string,
	gpuAvailable bool,
	gpuFn func() (T, error),
	cpuFn func() (T, error),
) (T, ComputeMode, error) {
	var zero T

	if gpuAvailable {
		result, err := gpuFn()
		if err == nil {
			return result, ComputeModeGPU, nil
		}

		// GPU failed - warn and fallback
		log.Printf("[%s] GPU execution failed: %v. Falling back to CPU.", operationName, err)
		atomic.AddInt64(&globalFallbackStats.CPUFallbacks, 1)

		cpuResult, cpuErr := cpuFn()
		if cpuErr != nil {
			return zero, ComputeModeUnknown, fmt.Errorf("%s: GPU failed (%v), CPU fallback also failed (%v)", operationName, err, cpuErr)
		}
		return cpuResult, ComputeModeCPU, nil
	}

	// GPU not available - use CPU
	result, err := cpuFn()
	if err != nil {
		return zero, ComputeModeCPU, fmt.Errorf("%s (CPU): %w", operationName, err)
	}
	atomic.AddInt64(&globalFallbackStats.CPUFallbacks, 1)
	return result, ComputeModeCPU, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// GPU DETECTION (Using qos Intel Level Zero)
// ═══════════════════════════════════════════════════════════════════════════

var (
	gpuDetected     bool
	gpuCheckDone    bool
	gpuCheckMutex   sync.Mutex
)

// detectGPU checks if GPU is available via qos Intel Level Zero
// Caches result to avoid repeated initialization attempts
//
// Implementation:
//   - Tries qos.InitializeGPU() once
//   - Caches result (success or failure)
//   - Returns cached value on subsequent calls
//
// Returns:
//   - true if GPU available and initialized
//   - false if GPU unavailable (CPU fallback)
func detectGPU() bool {
	gpuCheckMutex.Lock()
	defer gpuCheckMutex.Unlock()

	// Return cached result if already checked
	if gpuCheckDone {
		return gpuDetected
	}

	// First time - try to initialize GPU
	gpu, err := qos.InitializeGPU()
	if err != nil {
		// GPU not available - this is NOT an error, just means we use CPU
		log.Printf("[GPU Detection] GPU not available: %v (using CPU fallback)", err)
		gpuDetected = false
		gpuCheckDone = true
		return false
	}

	// GPU available!
	// Clean up the test GPU (we'll reinitialize when actually needed)
	defer gpu.Destroy()

	props, _ := gpu.GetDeviceProperties()
	log.Printf("[GPU Detection] GPU available: %v", props)

	gpuDetected = true
	gpuCheckDone = true
	return true
}
