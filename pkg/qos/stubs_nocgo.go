//go:build !cgo
// +build !cgo

// Package qos - No-CGo stubs for types that require Level Zero
// When Level Zero headers not available, these stubs provide compilation
// All functions return "GPU not available" errors gracefully
package qos

import (
	"fmt"
)

// ═══════════════════════════════════════════════════════════════════════════
// OPTIMIZED QUATERNION EXECUTOR STUBS
// ═══════════════════════════════════════════════════════════════════════════

// OptimizedQuaternionExecutor stub (requires GPU)
type OptimizedQuaternionExecutor struct {
	stub bool
}

// NewOptimizedQuaternionExecutor stub
func NewOptimizedQuaternionExecutor(gpu *GPU) (*OptimizedQuaternionExecutor, error) {
	return nil, fmt.Errorf("OptimizedQuaternionExecutor requires GPU - Level Zero not available")
}

// BatchSLERP stub
func (e *OptimizedQuaternionExecutor) BatchSLERP(pairs [][2]Quaternion, t float64) ([]Quaternion, error) {
	return nil, fmt.Errorf("GPU not available")
}

// BatchMultiply stub
func (e *OptimizedQuaternionExecutor) BatchMultiply(pairs [][2]Quaternion) ([]Quaternion, error) {
	return nil, fmt.Errorf("GPU not available")
}

// BatchNormalize stub
func (e *OptimizedQuaternionExecutor) BatchNormalize(quaternions []Quaternion) ([]Quaternion, error) {
	return nil, fmt.Errorf("GPU not available")
}

// Execute stub
func (e *OptimizedQuaternionExecutor) Execute(input, target []Quaternion, dt, foldStrength float32) ([]Quaternion, error) {
	return nil, fmt.Errorf("GPU not available")
}

// Flush stub
func (e *OptimizedQuaternionExecutor) Flush() error {
	return nil
}

// Destroy stub
func (e *OptimizedQuaternionExecutor) Destroy() {
	// Nothing to do
}

// SetBatchSize stub
func (e *OptimizedQuaternionExecutor) SetBatchSize(size int) {
	// Nothing to do
}

// ═══════════════════════════════════════════════════════════════════════════
// SAT ORIGAMI GPU STUBS
// ═══════════════════════════════════════════════════════════════════════════

// SATOrigamiGPU stub (requires GPU)
type SATOrigamiGPU struct {
	stub bool
}

// NewSATOrigamiGPU stub
func NewSATOrigamiGPU(numVars int, clauseRatio float64, gpu *GPU, kernel *KernelModule) (*SATOrigamiGPU, error) {
	return nil, fmt.Errorf("SATOrigamiGPU requires GPU - Level Zero not available")
}

// Solve stub
func (s *SATOrigamiGPU) Solve(maxIterations int) ([]bool, float64, error) {
	return nil, 0.0, fmt.Errorf("GPU not available")
}

// GetStats stub
func (s *SATOrigamiGPU) GetStats() map[string]interface{} {
	return map[string]interface{}{
		"error": "GPU not available",
	}
}

// Destroy stub
func (s *SATOrigamiGPU) Destroy() {
	// Nothing to do
}

// ═══════════════════════════════════════════════════════════════════════════
// ASYNC EXECUTOR STUBS
// ═══════════════════════════════════════════════════════════════════════════

// AsyncDoubleBufferExecutor stub
type AsyncDoubleBufferExecutor struct {
	stub bool
}

// NewAsyncDoubleBufferExecutor stub
func NewAsyncDoubleBufferExecutor(gpu *GPU, kernel *KernelModule, capacity int) (*AsyncDoubleBufferExecutor, error) {
	return nil, fmt.Errorf("AsyncDoubleBufferExecutor requires GPU - Level Zero not available")
}

// Submit stub
func (e *AsyncDoubleBufferExecutor) Submit(input, target []Quaternion, dt, foldStrength float32) error {
	return fmt.Errorf("GPU not available")
}

// Sync stub
func (e *AsyncDoubleBufferExecutor) Sync() ([]Quaternion, error) {
	return nil, fmt.Errorf("GPU not available")
}

// Destroy stub
func (e *AsyncDoubleBufferExecutor) Destroy() {
	// Nothing to do
}

// GetStats stub
func (e *AsyncDoubleBufferExecutor) GetStats() map[string]interface{} {
	return map[string]interface{}{
		"error": "GPU not available",
	}
}
