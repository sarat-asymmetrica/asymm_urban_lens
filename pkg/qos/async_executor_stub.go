//go:build !cgo
// +build !cgo

// Package qos - Async Executor Stub (no CGo)
package qos

import "fmt"

var errGPUNotAvailable = fmt.Errorf("GPU not available - Level Zero drivers not installed")

// AsyncExecutor stub type
type AsyncExecutor struct {
	stub bool
}

// NewAsyncExecutor stub
func NewAsyncExecutor(gpu *GPU) (*AsyncExecutor, error) {
	return nil, errGPUNotAvailable
}

// ExecuteAsync stub
func (ae *AsyncExecutor) ExecuteAsync(data []byte) error {
	return errGPUNotAvailable
}

// Wait stub
func (ae *AsyncExecutor) Wait() error {
	return nil
}

// Destroy stub
func (ae *AsyncExecutor) Destroy() {
	// Nothing to do
}
