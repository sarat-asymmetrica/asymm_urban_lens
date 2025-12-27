//go:build !cgo
// +build !cgo

// Package qos - GPU stub (no CGo for initial compilation)
// Wave 1: Placeholder until Level Zero drivers available
package qos

import (
	"fmt"
	"unsafe"
)

// GPU represents Intel Level Zero GPU context (stub)
type GPU struct {
	stub bool
}

// InitializeGPU stub
func InitializeGPU() (*GPU, error) {
	return nil, fmt.Errorf("GPU not available - Level Zero drivers not installed")
}

// AllocateDeviceMemory stub
func (g *GPU) AllocateDeviceMemory(size uint64) (unsafe.Pointer, error) {
	return nil, fmt.Errorf("GPU not available")
}

// AllocateSharedMemory stub
func (g *GPU) AllocateSharedMemory(size uint64) (unsafe.Pointer, error) {
	return nil, fmt.Errorf("GPU not available")
}

// CopyToDevice stub
func (g *GPU) CopyToDevice(dst unsafe.Pointer, src unsafe.Pointer, size uint64) error {
	return fmt.Errorf("GPU not available")
}

// CopyFromDevice stub
func (g *GPU) CopyFromDevice(dst unsafe.Pointer, src unsafe.Pointer, size uint64) error {
	return fmt.Errorf("GPU not available")
}

// ExecuteCommandList stub
func (g *GPU) ExecuteCommandList() error {
	return fmt.Errorf("GPU not available")
}

// FreeMemory stub
func (g *GPU) FreeMemory(ptr unsafe.Pointer) error {
	return nil
}

// Destroy stub
func (g *GPU) Destroy() error {
	return nil
}

// GetDeviceProperties stub
func (g *GPU) GetDeviceProperties() (map[string]interface{}, error) {
	return nil, fmt.Errorf("GPU not available")
}

// LoadKernel stub
func (g *GPU) LoadKernel(spirvPath string, kernelName string) (*KernelModule, error) {
	return nil, fmt.Errorf("GPU not available")
}

// KernelModule stub
type KernelModule struct {
	gpu  *GPU
	name string
}

// SetKernelArg stub
func (km *KernelModule) SetKernelArg(argIndex uint32, size uint64, value unsafe.Pointer) error {
	return fmt.Errorf("GPU not available")
}

// SetGroupSize stub
func (km *KernelModule) SetGroupSize(groupSizeX, groupSizeY, groupSizeZ uint32) error {
	return fmt.Errorf("GPU not available")
}

// SuggestGroupSize stub
func (km *KernelModule) SuggestGroupSize(globalSizeX, globalSizeY, globalSizeZ uint32) (uint32, uint32, uint32, error) {
	return 256, 1, 1, nil
}

// Dispatch stub
func (km *KernelModule) Dispatch(numGroupsX, numGroupsY, numGroupsZ uint32) error {
	return fmt.Errorf("GPU not available")
}

// DispatchAsync stub
func (km *KernelModule) DispatchAsync(numGroupsX, numGroupsY, numGroupsZ uint32) error {
	return fmt.Errorf("GPU not available")
}

// WaitForCompletion stub
func (km *KernelModule) WaitForCompletion() error {
	return fmt.Errorf("GPU not available")
}

// GetKernelProperties stub
func (km *KernelModule) GetKernelProperties() (map[string]interface{}, error) {
	return nil, fmt.Errorf("GPU not available")
}

// Destroy stub
func (km *KernelModule) Destroy() {
	// Nothing to do
}

// QuaternionKernelHelper stub
type QuaternionKernelHelper struct {
	kernel *KernelModule
	n      int
}

// NewQuaternionKernelHelper stub
func NewQuaternionKernelHelper(kernel *KernelModule, n int) (*QuaternionKernelHelper, error) {
	return nil, fmt.Errorf("GPU not available")
}

// Execute stub
func (qkh *QuaternionKernelHelper) Execute(input, target []Quaternion, dt, foldStrength float32) ([]Quaternion, error) {
	return nil, fmt.Errorf("GPU not available")
}

// Destroy stub
func (qkh *QuaternionKernelHelper) Destroy() {
	// Nothing to do
}
