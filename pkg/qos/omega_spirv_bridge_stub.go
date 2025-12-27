//go:build !cgo
// +build !cgo

package qos

// default runner for non-CGo builds: rely entirely on CPU Omega Lattice path.
type defaultSPIRVRunner struct{}

func newDefaultSPIRVRunner() spirvKernelExecutor {
	return defaultSPIRVRunner{}
}

func (defaultSPIRVRunner) RunGeodesic(current, target []Quaternion, cfg OmegaSPIRVConfig) ([]Quaternion, OmegaSPIRVResult, error) {
	// GPU unavailable in stub builds; signal fallback.
	return nil, OmegaSPIRVResult{GPUUsed: false, Notes: "Level Zero unavailable in !cgo build"}, nil
}
