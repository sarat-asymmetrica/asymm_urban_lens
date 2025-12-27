//go:build cgo
// +build cgo

package qos

import (
	"fmt"
	"path/filepath"
)

// default runner for CGo builds: attempt GPU dispatch, gracefully fall back.
type defaultSPIRVRunner struct{}

func newDefaultSPIRVRunner() spirvKernelExecutor {
	return defaultSPIRVRunner{}
}

func (defaultSPIRVRunner) RunGeodesic(current, target []Quaternion, cfg OmegaSPIRVConfig) ([]Quaternion, OmegaSPIRVResult, error) {
	gpu, err := InitializeGPU()
	if err != nil {
		return nil, OmegaSPIRVResult{GPUUsed: false, Notes: "GPU initialization failed, using CPU"}, nil
	}
	defer gpu.Destroy()

	kernelPath := filepath.Join(
		"kernels",
		"slerp_evolution_optimized.spv",
	)

	kernel, err := gpu.LoadKernel(kernelPath, "slerp_evolution")
	if err != nil {
		return nil, OmegaSPIRVResult{GPUUsed: false, Notes: fmt.Sprintf("LoadKernel failed: %v", err)}, nil
	}
	defer kernel.Destroy()

	helper, err := NewQuaternionKernelHelper(gpu, kernel, len(current))
	if err != nil {
		return nil, OmegaSPIRVResult{GPUUsed: false, Notes: fmt.Sprintf("Kernel helper init failed: %v", err)}, nil
	}
	defer helper.Destroy()

	out, err := helper.Execute(current, target, cfg.DT, cfg.FoldStrength)
	if err != nil {
		return nil, OmegaSPIRVResult{GPUUsed: false, Notes: fmt.Sprintf("Kernel execute failed: %v", err)}, nil
	}

	return out, OmegaSPIRVResult{
		GPUUsed:    true,
		KernelPath: kernelPath,
		KernelName: "slerp_evolution",
		Notes:      "SPIR-V geodesic evolution executed",
	}, nil
}
