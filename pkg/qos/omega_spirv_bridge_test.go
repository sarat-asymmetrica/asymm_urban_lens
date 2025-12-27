package qos

import (
	"testing"
)

type fakeRunner struct {
	output []Quaternion
	res    OmegaSPIRVResult
	err    error
	calls  int
}

func (f *fakeRunner) RunGeodesic(current, target []Quaternion, cfg OmegaSPIRVConfig) ([]Quaternion, OmegaSPIRVResult, error) {
	f.calls++
	return f.output, f.res, f.err
}

func TestOmegaBridgeFallsBackToOmegaLattice(t *testing.T) {
	bridge := NewOmegaSPIRVBridgeWithRunner(nil)

	current := []Quaternion{{W: 1, X: 0, Y: 0, Z: 0}}
	target := []Quaternion{{W: 0, X: 1, Y: 0, Z: 0}}

	out, res, err := bridge.EvolveGeodesic(current, target, OmegaSPIRVConfig{DT: 0.05, FoldStrength: 0.5})
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if res.GPUUsed {
		t.Fatalf("expected CPU fallback, got GPU execution")
	}
	if len(out) != 1 {
		t.Fatalf("expected one output quaternion, got %d", len(out))
	}

	if out[0].Norm() < 0.999 || out[0].Norm() > 1.001 {
		t.Fatalf("output quaternion not normalized: %f", out[0].Norm())
	}
}

func TestOmegaBridgePrefersKernelWhenProvided(t *testing.T) {
	expected := []Quaternion{{W: 0, X: 0, Y: 1, Z: 0}}
	runner := &fakeRunner{
		output: expected,
		res: OmegaSPIRVResult{
			GPUUsed:    true,
			KernelName: "slerp_evolution",
			KernelPath: "test.spv",
		},
	}

	bridge := NewOmegaSPIRVBridgeWithRunner(runner)
	current := []Quaternion{{W: 1, X: 0, Y: 0, Z: 0}}
	target := []Quaternion{{W: 0, X: 1, Y: 0, Z: 0}}

	out, res, err := bridge.EvolveGeodesic(current, target, DefaultOmegaSPIRVConfig())
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !res.GPUUsed {
		t.Fatalf("expected GPU path to be honored")
	}
	if runner.calls != 1 {
		t.Fatalf("expected runner to be invoked once, got %d", runner.calls)
	}
	if out[0] != expected[0] {
		t.Fatalf("bridge should return runner output: %+v", out[0])
	}
}

func BenchmarkOmegaBridgeCPUFallback(b *testing.B) {
	bridge := NewOmegaSPIRVBridgeWithRunner(nil)

	current := make([]Quaternion, 256)
	target := make([]Quaternion, 256)
	for i := range current {
		current[i] = Quaternion{W: 1, X: 0, Y: 0, Z: 0}
		target[i] = Quaternion{W: 0, X: 1, Y: 0, Z: 0}
	}

	cfg := OmegaSPIRVConfig{DT: 0.02, FoldStrength: 0.6}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if _, _, err := bridge.EvolveGeodesic(current, target, cfg); err != nil {
			b.Fatalf("unexpected error: %v", err)
		}
	}
}
