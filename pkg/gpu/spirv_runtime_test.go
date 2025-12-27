// Package gpu - SPIR-V Runtime Tests
// Validates kernel loading, execution, and CPU emulation
package gpu

import (
	"math"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// RUNTIME INITIALIZATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestNewSPIRVRuntime(t *testing.T) {
	runtime := NewSPIRVRuntime()
	if runtime == nil {
		t.Fatal("NewSPIRVRuntime returned nil")
	}

	if runtime.kernels == nil {
		t.Error("kernels map not initialized")
	}

	if runtime.stats == nil {
		t.Error("stats not initialized")
	}

	// Backend should be CPU (GPU not available in CI)
	if runtime.backend != BackendCPU {
		t.Logf("Backend: %s (expected CPU in test environment)", runtime.backend)
	}
}

func TestGetRuntime(t *testing.T) {
	runtime1 := GetRuntime()
	runtime2 := GetRuntime()

	if runtime1 != runtime2 {
		t.Error("GetRuntime should return same instance (singleton)")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// KERNEL LOADING TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestLoadSPIRVKernel(t *testing.T) {
	runtime := NewSPIRVRuntime()

	// Try to load slerp_evolution kernel
	kernel, err := runtime.LoadSPIRVKernel("slerp_evolution")
	if err != nil {
		t.Skipf("Kernel not found (expected in CI): %v", err)
		return
	}

	if kernel == nil {
		t.Fatal("LoadSPIRVKernel returned nil kernel")
	}

	if kernel.Name != "slerp_evolution" {
		t.Errorf("kernel.Name = %s, want slerp_evolution", kernel.Name)
	}

	if kernel.Type != KernelTypeSLERP {
		t.Errorf("kernel.Type = %s, want %s", kernel.Type, KernelTypeSLERP)
	}

	if len(kernel.Data) == 0 {
		t.Error("kernel.Data is empty")
	}

	// Validate SPIR-V magic number
	if len(kernel.Data) >= 4 {
		magic := uint32(kernel.Data[0]) | uint32(kernel.Data[1])<<8 |
			uint32(kernel.Data[2])<<16 | uint32(kernel.Data[3])<<24
		const spirvMagic = 0x07230203
		if magic != spirvMagic {
			t.Errorf("Invalid SPIR-V magic: got 0x%08X, want 0x%08X", magic, spirvMagic)
		}
	}
}

func TestLoadSPIRVKernel_Caching(t *testing.T) {
	runtime := NewSPIRVRuntime()

	kernel1, err1 := runtime.LoadSPIRVKernel("slerp_evolution")
	if err1 != nil {
		t.Skip("Kernel not available")
		return
	}

	kernel2, err2 := runtime.LoadSPIRVKernel("slerp_evolution")
	if err2 != nil {
		t.Fatal("Second load failed:", err2)
	}

	if kernel1 != kernel2 {
		t.Error("Kernel should be cached (same instance)")
	}

	if runtime.stats.KernelsLoaded != 1 {
		t.Errorf("KernelsLoaded = %d, want 1 (cached load shouldn't increment)", runtime.stats.KernelsLoaded)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CPU EMULATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestEmulateSLERP(t *testing.T) {
	runtime := NewSPIRVRuntime()

	// Test quaternion pair
	q0 := Quaternion{W: 1, X: 0, Y: 0, Z: 0} // Identity
	q1 := Quaternion{W: 0.7071, X: 0.7071, Y: 0, Z: 0} // 90° rotation around X

	input := []float32{
		float32(q0.W), float32(q0.X), float32(q0.Y), float32(q0.Z),
		float32(q1.W), float32(q1.X), float32(q1.Y), float32(q1.Z),
	}

	output, err := runtime.emulateSLERP(input)
	if err != nil {
		t.Fatal("emulateSLERP failed:", err)
	}

	if len(output) != 4 {
		t.Fatalf("output length = %d, want 4", len(output))
	}

	// Result should be halfway between q0 and q1 (t=0.5)
	// At t=0.5, should be ~45° rotation
	result := Quaternion{
		W: float64(output[0]),
		X: float64(output[1]),
		Y: float64(output[2]),
		Z: float64(output[3]),
	}

	// Check result is on S³
	norm := result.Norm()
	if math.Abs(norm-1.0) > 0.001 {
		t.Errorf("result norm = %f, want ~1.0", norm)
	}

	// Result should be between q0 and q1
	if result.W < q1.W || result.W > q0.W {
		t.Errorf("result.W = %f, should be between %f and %f", result.W, q1.W, q0.W)
	}
}

func TestEmulateMultiply(t *testing.T) {
	runtime := NewSPIRVRuntime()

	q1 := Quaternion{W: 1, X: 0, Y: 0, Z: 0} // Identity
	q2 := Quaternion{W: 0.7071, X: 0.7071, Y: 0, Z: 0} // 90° rotation

	input := []float32{
		float32(q1.W), float32(q1.X), float32(q1.Y), float32(q1.Z),
		float32(q2.W), float32(q2.X), float32(q2.Y), float32(q2.Z),
	}

	output, err := runtime.emulateMultiply(input)
	if err != nil {
		t.Fatal("emulateMultiply failed:", err)
	}

	if len(output) != 4 {
		t.Fatalf("output length = %d, want 4", len(output))
	}

	// Identity × q = q
	expected := q2
	result := Quaternion{
		W: float64(output[0]),
		X: float64(output[1]),
		Y: float64(output[2]),
		Z: float64(output[3]),
	}

	tolerance := 0.0001
	if math.Abs(result.W-expected.W) > tolerance ||
		math.Abs(result.X-expected.X) > tolerance ||
		math.Abs(result.Y-expected.Y) > tolerance ||
		math.Abs(result.Z-expected.Z) > tolerance {
		t.Errorf("result = %+v, want %+v", result, expected)
	}
}

func TestEmulateNormalize(t *testing.T) {
	runtime := NewSPIRVRuntime()

	// Unnormalized quaternion
	q := Quaternion{W: 2, X: 3, Y: 4, Z: 5}

	input := []float32{
		float32(q.W), float32(q.X), float32(q.Y), float32(q.Z),
	}

	output, err := runtime.emulateNormalize(input)
	if err != nil {
		t.Fatal("emulateNormalize failed:", err)
	}

	if len(output) != 4 {
		t.Fatalf("output length = %d, want 4", len(output))
	}

	result := Quaternion{
		W: float64(output[0]),
		X: float64(output[1]),
		Y: float64(output[2]),
		Z: float64(output[3]),
	}

	// Check norm = 1.0
	norm := result.Norm()
	if math.Abs(norm-1.0) > 0.0001 {
		t.Errorf("result norm = %f, want 1.0", norm)
	}

	// Direction should be preserved
	expectedNormalized := q.Normalize()
	tolerance := 0.0001
	if math.Abs(result.W-expectedNormalized.W) > tolerance ||
		math.Abs(result.X-expectedNormalized.X) > tolerance ||
		math.Abs(result.Y-expectedNormalized.Y) > tolerance ||
		math.Abs(result.Z-expectedNormalized.Z) > tolerance {
		t.Errorf("result = %+v, want %+v", result, expectedNormalized)
	}
}

func TestEmulateDistance(t *testing.T) {
	runtime := NewSPIRVRuntime()

	// Two quaternions
	q0 := Quaternion{W: 1, X: 0, Y: 0, Z: 0} // Identity
	q1 := Quaternion{W: 0, X: 1, Y: 0, Z: 0} // 180° rotation

	input := []float32{
		float32(q0.W), float32(q0.X), float32(q0.Y), float32(q0.Z),
		float32(q1.W), float32(q1.X), float32(q1.Y), float32(q1.Z),
	}

	output, err := runtime.emulateDistance(input)
	if err != nil {
		t.Fatal("emulateDistance failed:", err)
	}

	if len(output) != 1 {
		t.Fatalf("output length = %d, want 1", len(output))
	}

	distance := float64(output[0])

	// Distance should be π/2 (90° geodesic)
	expectedDistance := math.Pi / 2
	if math.Abs(distance-expectedDistance) > 0.01 {
		t.Errorf("distance = %f, want %f", distance, expectedDistance)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// KERNEL EXECUTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestExecuteKernel_SLERP(t *testing.T) {
	runtime := NewSPIRVRuntime()

	// Create a simple kernel (CPU emulation)
	kernel := &Kernel{
		Name:    "test_slerp",
		Type:    KernelTypeSLERP,
		Backend: BackendCPU,
	}

	q0 := Quaternion{W: 1, X: 0, Y: 0, Z: 0}
	q1 := Quaternion{W: 0.7071, X: 0.7071, Y: 0, Z: 0}

	input := []float32{
		float32(q0.W), float32(q0.X), float32(q0.Y), float32(q0.Z),
		float32(q1.W), float32(q1.X), float32(q1.Y), float32(q1.Z),
	}

	output, err := runtime.ExecuteKernel(kernel, input)
	if err != nil {
		t.Fatal("ExecuteKernel failed:", err)
	}

	if len(output) != 4 {
		t.Fatalf("output length = %d, want 4", len(output))
	}

	// Verify output is valid quaternion
	result := Quaternion{
		W: float64(output[0]),
		X: float64(output[1]),
		Y: float64(output[2]),
		Z: float64(output[3]),
	}

	norm := result.Norm()
	if math.Abs(norm-1.0) > 0.001 {
		t.Errorf("result norm = %f, want ~1.0", norm)
	}
}

func TestExecuteKernel_EmptyInput(t *testing.T) {
	runtime := NewSPIRVRuntime()

	kernel := &Kernel{
		Name:    "test",
		Type:    KernelTypeSLERP,
		Backend: BackendCPU,
	}

	output, err := runtime.ExecuteKernel(kernel, []float32{})
	if err != nil {
		t.Fatal("ExecuteKernel with empty input failed:", err)
	}

	if len(output) != 0 {
		t.Errorf("output length = %d, want 0", len(output))
	}
}

func TestExecuteKernel_InvalidInput(t *testing.T) {
	runtime := NewSPIRVRuntime()

	kernel := &Kernel{
		Name:    "test",
		Type:    KernelTypeSLERP,
		Backend: BackendCPU,
	}

	// Input not multiple of 4
	input := []float32{1, 2, 3}

	_, err := runtime.ExecuteKernel(kernel, input)
	if err == nil {
		t.Error("ExecuteKernel should fail with invalid input size")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// BATCH PROCESSING TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestBatchSLERP(t *testing.T) {
	runtime := NewSPIRVRuntime()

	numPairs := 100
	input := make([]float32, numPairs*8)

	for i := 0; i < numPairs; i++ {
		base := i * 8
		// q0 = identity
		input[base+0] = 1
		input[base+1] = 0
		input[base+2] = 0
		input[base+3] = 0
		// q1 = 90° rotation
		input[base+4] = 0.7071
		input[base+5] = 0.7071
		input[base+6] = 0
		input[base+7] = 0
	}

	output, err := runtime.emulateSLERP(input)
	if err != nil {
		t.Fatal("batch SLERP failed:", err)
	}

	if len(output) != numPairs*4 {
		t.Fatalf("output length = %d, want %d", len(output), numPairs*4)
	}

	// Verify all outputs are valid quaternions
	for i := 0; i < numPairs; i++ {
		base := i * 4
		q := Quaternion{
			W: float64(output[base+0]),
			X: float64(output[base+1]),
			Y: float64(output[base+2]),
			Z: float64(output[base+3]),
		}

		norm := q.Norm()
		if math.Abs(norm-1.0) > 0.001 {
			t.Errorf("quaternion %d: norm = %f, want ~1.0", i, norm)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// STATISTICS TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestRuntimeStats(t *testing.T) {
	runtime := NewSPIRVRuntime()

	initialStats := runtime.GetStats()
	if initialStats.TotalOperations != 0 {
		t.Errorf("initial TotalOperations = %d, want 0", initialStats.TotalOperations)
	}

	// Execute a kernel
	kernel := &Kernel{
		Name:    "test",
		Type:    KernelTypeSLERP,
		Backend: BackendCPU,
	}

	input := make([]float32, 8) // 1 pair
	_, _ = runtime.ExecuteKernel(kernel, input)

	stats := runtime.GetStats()
	if stats.TotalOperations != 1 {
		t.Errorf("TotalOperations = %d, want 1", stats.TotalOperations)
	}

	if stats.ExecutionsCPU != 1 {
		t.Errorf("ExecutionsCPU = %d, want 1", stats.ExecutionsCPU)
	}
}

func TestGetKernelInfo(t *testing.T) {
	runtime := NewSPIRVRuntime()

	kernel := &Kernel{
		Name:    "test_kernel",
		Data:    make([]byte, 1000),
		Type:    KernelTypeSLERP,
		Backend: BackendCPU,
	}

	info := runtime.GetKernelInfo(kernel)

	if info.Name != "test_kernel" {
		t.Errorf("info.Name = %s, want test_kernel", info.Name)
	}

	if info.Size != 1000 {
		t.Errorf("info.Size = %d, want 1000", info.Size)
	}

	if !info.Available {
		t.Error("info.Available should be true")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// PERFORMANCE TESTS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkSLERPCPU_100(b *testing.B) {
	runtime := NewSPIRVRuntime()

	input := make([]float32, 100*8)
	for i := 0; i < 100; i++ {
		base := i * 8
		input[base+0] = 1
		input[base+4] = 0.7071
		input[base+5] = 0.7071
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = runtime.emulateSLERP(input)
	}
}

func BenchmarkSLERPCPU_1000(b *testing.B) {
	runtime := NewSPIRVRuntime()

	input := make([]float32, 1000*8)
	for i := 0; i < 1000; i++ {
		base := i * 8
		input[base+0] = 1
		input[base+4] = 0.7071
		input[base+5] = 0.7071
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = runtime.emulateSLERP(input)
	}
}

func BenchmarkMultiplyCPU_1000(b *testing.B) {
	runtime := NewSPIRVRuntime()

	input := make([]float32, 1000*8)
	for i := 0; i < 1000; i++ {
		base := i * 8
		input[base+0] = 1
		input[base+4] = 0.7071
		input[base+5] = 0.7071
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = runtime.emulateMultiply(input)
	}
}
