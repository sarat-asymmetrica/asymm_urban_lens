//go:build !cgo
// +build !cgo

// Package qos - Persistent Buffers Stub (no CGo)
package qos

import (
	"fmt"
	"unsafe"
)

var errGPUNotAvailablePB = fmt.Errorf("GPU not available - Level Zero drivers not installed")

// PersistentBuffer stub type
type PersistentBuffer struct {
	stub bool
}

// NewPersistentBuffer stub
func NewPersistentBuffer(gpu *GPU, size uint64) (*PersistentBuffer, error) {
	return nil, errGPUNotAvailablePB
}

// GetHostPointer stub
func (pb *PersistentBuffer) GetHostPointer() unsafe.Pointer {
	return nil
}

// GetDevicePointer stub
func (pb *PersistentBuffer) GetDevicePointer() unsafe.Pointer {
	return nil
}

// Sync stub
func (pb *PersistentBuffer) Sync() error {
	return errGPUNotAvailablePB
}

// Destroy stub
func (pb *PersistentBuffer) Destroy() {
	// Nothing to do
}
