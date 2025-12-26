// Package gpu - GPU Accelerator with automatic fallback
// Provides GPU-accelerated operations when available, CPU fallback otherwise
package gpu

import (
	"sync"
	"time"
)

// Accelerator provides GPU-accelerated quaternion operations
type Accelerator struct {
	gpuAvailable bool
	stats        *AcceleratorStats
	mu           sync.RWMutex
}

// AcceleratorStats tracks performance metrics
type AcceleratorStats struct {
	TotalOps      int64
	GPUOps        int64
	CPUOps        int64
	TotalDuration time.Duration
	OpsPerSecond  float64
}

// NewAccelerator creates a new GPU accelerator
// Automatically detects GPU availability
func NewAccelerator() *Accelerator {
	return &Accelerator{
		gpuAvailable: detectGPU(),
		stats:        &AcceleratorStats{},
	}
}

// detectGPU checks if GPU acceleration is available
// Currently returns false - GPU support requires Level Zero bindings
func detectGPU() bool {
	// TODO: Implement Level Zero GPU detection
	// For now, use CPU fallback
	return false
}

// IsGPUAvailable returns true if GPU acceleration is available
func (a *Accelerator) IsGPUAvailable() bool {
	return a.gpuAvailable
}

// BatchSLERP performs SLERP on multiple quaternion pairs
// Uses GPU when available, CPU otherwise
func (a *Accelerator) BatchSLERP(pairs [][2]Quaternion, t float32) []Quaternion {
	start := time.Now()
	results := make([]Quaternion, len(pairs))

	if a.gpuAvailable {
		// GPU path (future implementation)
		results = a.batchSLERPGPU(pairs, t)
		a.recordOp(len(pairs), true, time.Since(start))
	} else {
		// CPU fallback
		for i, pair := range pairs {
			results[i] = SLERP(pair[0], pair[1], t)
		}
		a.recordOp(len(pairs), false, time.Since(start))
	}

	return results
}

// BatchMultiply performs quaternion multiplication on multiple pairs
func (a *Accelerator) BatchMultiply(pairs [][2]Quaternion) []Quaternion {
	start := time.Now()
	results := make([]Quaternion, len(pairs))

	if a.gpuAvailable {
		results = a.batchMultiplyGPU(pairs)
		a.recordOp(len(pairs), true, time.Since(start))
	} else {
		for i, pair := range pairs {
			results[i] = pair[0].Multiply(pair[1])
		}
		a.recordOp(len(pairs), false, time.Since(start))
	}

	return results
}

// BatchNormalize normalizes multiple quaternions
func (a *Accelerator) BatchNormalize(quaternions []Quaternion) []Quaternion {
	start := time.Now()
	results := make([]Quaternion, len(quaternions))

	if a.gpuAvailable {
		results = a.batchNormalizeGPU(quaternions)
		a.recordOp(len(quaternions), true, time.Since(start))
	} else {
		for i, q := range quaternions {
			results[i] = q.Normalize()
		}
		a.recordOp(len(quaternions), false, time.Since(start))
	}

	return results
}

// BatchRotateVectors rotates multiple vectors by a quaternion
func (a *Accelerator) BatchRotateVectors(q Quaternion, vectors [][3]float32) [][3]float32 {
	start := time.Now()
	results := make([][3]float32, len(vectors))

	if a.gpuAvailable {
		results = a.batchRotateGPU(q, vectors)
		a.recordOp(len(vectors), true, time.Since(start))
	} else {
		for i, v := range vectors {
			results[i] = q.RotateVector(v)
		}
		a.recordOp(len(vectors), false, time.Since(start))
	}

	return results
}

// GPU implementations (stubs for now)

func (a *Accelerator) batchSLERPGPU(pairs [][2]Quaternion, t float32) []Quaternion {
	// TODO: Implement with Level Zero SPIR-V kernel
	results := make([]Quaternion, len(pairs))
	for i, pair := range pairs {
		results[i] = SLERP(pair[0], pair[1], t)
	}
	return results
}

func (a *Accelerator) batchMultiplyGPU(pairs [][2]Quaternion) []Quaternion {
	// TODO: Implement with Level Zero SPIR-V kernel
	results := make([]Quaternion, len(pairs))
	for i, pair := range pairs {
		results[i] = pair[0].Multiply(pair[1])
	}
	return results
}

func (a *Accelerator) batchNormalizeGPU(quaternions []Quaternion) []Quaternion {
	// TODO: Implement with Level Zero SPIR-V kernel
	results := make([]Quaternion, len(quaternions))
	for i, q := range quaternions {
		results[i] = q.Normalize()
	}
	return results
}

func (a *Accelerator) batchRotateGPU(q Quaternion, vectors [][3]float32) [][3]float32 {
	// TODO: Implement with Level Zero SPIR-V kernel
	results := make([][3]float32, len(vectors))
	for i, v := range vectors {
		results[i] = q.RotateVector(v)
	}
	return results
}

// recordOp records operation statistics
func (a *Accelerator) recordOp(count int, gpu bool, duration time.Duration) {
	a.mu.Lock()
	defer a.mu.Unlock()

	a.stats.TotalOps += int64(count)
	a.stats.TotalDuration += duration

	if gpu {
		a.stats.GPUOps += int64(count)
	} else {
		a.stats.CPUOps += int64(count)
	}

	if a.stats.TotalDuration > 0 {
		a.stats.OpsPerSecond = float64(a.stats.TotalOps) / a.stats.TotalDuration.Seconds()
	}
}

// GetStats returns current accelerator statistics
func (a *Accelerator) GetStats() *AcceleratorStats {
	a.mu.RLock()
	defer a.mu.RUnlock()
	return &AcceleratorStats{
		TotalOps:      a.stats.TotalOps,
		GPUOps:        a.stats.GPUOps,
		CPUOps:        a.stats.CPUOps,
		TotalDuration: a.stats.TotalDuration,
		OpsPerSecond:  a.stats.OpsPerSecond,
	}
}

// GetStatus returns accelerator status for API
func (a *Accelerator) GetStatus() map[string]interface{} {
	stats := a.GetStats()
	return map[string]interface{}{
		"gpu_available": a.gpuAvailable,
		"backend":       a.getBackendName(),
		"stats": map[string]interface{}{
			"total_ops":      stats.TotalOps,
			"gpu_ops":        stats.GPUOps,
			"cpu_ops":        stats.CPUOps,
			"ops_per_second": stats.OpsPerSecond,
		},
	}
}

func (a *Accelerator) getBackendName() string {
	if a.gpuAvailable {
		return "Level Zero (Intel GPU)"
	}
	return "CPU (fallback)"
}
