package qos

import (
	"github.com/asymmetrica/urbanlens/pkg/foundation/omega_lattice"
	"github.com/asymmetrica/urbanlens/pkg/foundation/substrate"
	"fmt"
	"math"
)

// OmegaSPIRVConfig captures the shared parameters between the Omega Lattice
// geodesic equation and the SPIR-V kernels that execute it on GPU hardware.
type OmegaSPIRVConfig struct {
	DT           float32
	FoldStrength float32
}

// DefaultOmegaSPIRVConfig returns a numerically stable set of defaults that
// mirror the kernel constants used in `slerp_evolution.cl` (60/40 fold/self).
func DefaultOmegaSPIRVConfig() OmegaSPIRVConfig {
	return OmegaSPIRVConfig{
		DT:           0.01,
		FoldStrength: 0.6,
	}
}

// OmegaSPIRVResult records how the bridge executed a geodesic step.
type OmegaSPIRVResult struct {
	GPUUsed    bool
	KernelPath string
	KernelName string
	Notes      string
}

// spirvKernelExecutor is implemented per build target so the bridge can defer
// to the GPU path when available while keeping CPU-only builds healthy.
type spirvKernelExecutor interface {
	RunGeodesic(current, target []Quaternion, cfg OmegaSPIRVConfig) ([]Quaternion, OmegaSPIRVResult, error)
}

// OmegaSPIRVBridge coordinates geodesic evolution between the SPIR-V kernels
// (when Level Zero is present) and the Omega Lattice reference path.
type OmegaSPIRVBridge struct {
	runner spirvKernelExecutor
}

// NewOmegaSPIRVBridge builds a bridge wired to the platform-specific runner.
func NewOmegaSPIRVBridge() *OmegaSPIRVBridge {
	return &OmegaSPIRVBridge{runner: newDefaultSPIRVRunner()}
}

// NewOmegaSPIRVBridgeWithRunner enables tests to inject a deterministic runner.
func NewOmegaSPIRVBridgeWithRunner(r spirvKernelExecutor) *OmegaSPIRVBridge {
	return &OmegaSPIRVBridge{runner: r}
}

// EvolveGeodesic advances `current` toward `target` using either the GPU kernel
// or the Omega Lattice CPU fallback. The returned result indicates whether the
// SPIR-V path executed.
func (b *OmegaSPIRVBridge) EvolveGeodesic(current, target []Quaternion, cfg OmegaSPIRVConfig) ([]Quaternion, OmegaSPIRVResult, error) {
	if len(current) != len(target) {
		return nil, OmegaSPIRVResult{}, fmt.Errorf("current (%d) and target (%d) lengths must match", len(current), len(target))
	}

	cfg = b.normalizeConfig(cfg)

	if b.runner != nil {
		out, res, err := b.runner.RunGeodesic(current, target, cfg)
		if err != nil && res.GPUUsed {
			return nil, res, err
		}
		if res.GPUUsed && err == nil {
			return out, res, nil
		}
	}

	return b.cpuGeodesic(current, target, cfg)
}

// BatchDistances computes the Omega Lattice angle between corresponding
// quaternions. This mirrors the `quaternion_distance_batch` kernel.
func (b *OmegaSPIRVBridge) BatchDistances(current, target []Quaternion) ([]float32, error) {
	if len(current) != len(target) {
		return nil, fmt.Errorf("current (%d) and target (%d) lengths must match", len(current), len(target))
	}

	distances := make([]float32, len(current))
	for i := range current {
		q0 := toSubstrate(current[i])
		q1 := toSubstrate(target[i])
		distances[i] = float32(omega_lattice.Angle(q0, q1))
	}
	return distances, nil
}

func (b *OmegaSPIRVBridge) normalizeConfig(cfg OmegaSPIRVConfig) OmegaSPIRVConfig {
	if cfg.DT == 0 {
		cfg.DT = DefaultOmegaSPIRVConfig().DT
	}
	if cfg.FoldStrength == 0 {
		cfg.FoldStrength = DefaultOmegaSPIRVConfig().FoldStrength
	}
	return cfg
}

func (b *OmegaSPIRVBridge) cpuGeodesic(current, target []Quaternion, cfg OmegaSPIRVConfig) ([]Quaternion, OmegaSPIRVResult, error) {
	step := math.Min(float64(cfg.DT*cfg.FoldStrength), 1.0)
	out := make([]Quaternion, len(current))

	for i := range current {
		q0 := toSubstrate(current[i])
		q1 := toSubstrate(target[i])

		folded := omega_lattice.OmegaSutraCorrected(q0, q1, step)
		self := q0.Mul(q0)
		combined := folded.Scale(0.6).Add(self.Scale(0.4)).Normalize()

		out[i] = fromSubstrate(combined)
	}

	return out, OmegaSPIRVResult{GPUUsed: false, Notes: "CPU fallback via Omega Lattice"}, nil
}

func toSubstrate(q Quaternion) substrate.Quaternion {
	return substrate.Quaternion{W: float64(q.W), X: float64(q.X), Y: float64(q.Y), Z: float64(q.Z)}
}

func fromSubstrate(q substrate.Quaternion) Quaternion {
	return Quaternion{W: float32(q.W), X: float32(q.X), Y: float32(q.Y), Z: float32(q.Z)}
}
