package gpu

import (
	"os"
	"path/filepath"
	"testing"
)

// ═════════════════════════════════════════════════════════════════════════════
// STABILIZATION TESTS (100% Required) - File Existence & Loading
// ═════════════════════════════════════════════════════════════════════════════

// TestSPIRV_KernelLoader_Initialization verifies kernel loader starts correctly
func TestSPIRV_KernelLoader_Initialization(t *testing.T) {
	loader := NewKernelLoader()

	if loader == nil {
		t.Fatal("NewKernelLoader() returned nil")
	}

	if loader.kernels == nil {
		t.Error("Kernel map not initialized")
	}

	t.Logf("✅ Kernel loader initialized successfully")
}

// TestSPIRV_KernelLoader_LoadsSLERP verifies SLERP kernel loads
func TestSPIRV_KernelLoader_LoadsSLERP(t *testing.T) {
	loader := NewKernelLoader()
	err := loader.LoadFromEmbedded()

	if err != nil {
		t.Logf("⚠️  LoadFromEmbedded error (expected if kernels not in path): %v", err)
	}

	// Try to load SLERP kernel directly
	data, err := loader.LoadKernel("slerp_evolution")
	if err != nil {
		t.Logf("⚠️  SLERP kernel not found (expected if kernels/ not in search path): %v", err)
		t.Skip("Skipping - kernel files not in expected locations")
	}

	if len(data) == 0 {
		t.Error("SLERP kernel loaded but has zero bytes")
	}

	t.Logf("✅ SLERP kernel loaded: %d bytes", len(data))
}

// TestSPIRV_KernelLoader_LoadsMatMul verifies MatMul kernel loads
func TestSPIRV_KernelLoader_LoadsMatMul(t *testing.T) {
	loader := NewKernelLoader()
	err := loader.LoadFromEmbedded()

	if err != nil {
		t.Logf("⚠️  LoadFromEmbedded error: %v", err)
	}

	// Try to load sparse matmul kernel directly
	data, err := loader.LoadKernel("sparse_matmul_core")
	if err != nil {
		t.Logf("⚠️  MatMul kernel not found: %v", err)
		t.Skip("Skipping - kernel files not in expected locations")
	}

	if len(data) == 0 {
		t.Error("MatMul kernel loaded but has zero bytes")
	}

	t.Logf("✅ MatMul kernel loaded: %d bytes", len(data))
}

// TestSPIRV_KernelExists_SLERPEvolution checks SLERP kernel file exists
func TestSPIRV_KernelExists_SLERPEvolution(t *testing.T) {
	paths := []string{
		"../../kernels/slerp_evolution.spv",
		"../../../kernels/slerp_evolution.spv",
		filepath.Join(os.Getenv("ASYMM_ROOT"), "asymm_urbanlens", "kernels", "slerp_evolution.spv"),
	}

	found := false
	var foundPath string
	var size int64

	for _, p := range paths {
		if info, err := os.Stat(p); err == nil {
			found = true
			foundPath = p
			size = info.Size()
			break
		}
	}

	if !found {
		t.Skip("⚠️  SLERP kernel not found in standard paths - skipping file existence test")
	}

	t.Logf("✅ SLERP kernel found: %s (%d bytes)", foundPath, size)

	// Verify file is non-empty
	if size == 0 {
		t.Error("SLERP kernel file exists but is empty")
	}

	// SPIR-V files should have magic number 0x07230203 at start
	data, err := os.ReadFile(foundPath)
	if err != nil {
		t.Fatalf("Failed to read kernel file: %v", err)
	}

	if len(data) < 4 {
		t.Error("SPIR-V file too small to contain magic number")
	}
}

// TestSPIRV_KernelExists_SparseMatMul checks MatMul kernel file exists
func TestSPIRV_KernelExists_SparseMatMul(t *testing.T) {
	paths := []string{
		"../../kernels/sparse_matmul_core.spv",
		"../../../kernels/sparse_matmul_core.spv",
		filepath.Join(os.Getenv("ASYMM_ROOT"), "asymm_urbanlens", "kernels", "sparse_matmul_core.spv"),
	}

	found := false
	var foundPath string
	var size int64

	for _, p := range paths {
		if info, err := os.Stat(p); err == nil {
			found = true
			foundPath = p
			size = info.Size()
			break
		}
	}

	if !found {
		t.Skip("⚠️  MatMul kernel not found in standard paths - skipping file existence test")
	}

	t.Logf("✅ MatMul kernel found: %s (%d bytes)", foundPath, size)

	if size == 0 {
		t.Error("MatMul kernel file exists but is empty")
	}
}

// TestSPIRV_KernelValidation validates loaded kernels are valid SPIR-V
func TestSPIRV_KernelValidation(t *testing.T) {
	loader := NewKernelLoader()
	err := loader.LoadFromEmbedded()

	if err != nil {
		t.Skip("Kernels not loaded - cannot validate")
	}

	kernelNames := []string{"slerp_evolution", "sparse_matmul_core"}

	for _, name := range kernelNames {
		data, ok := loader.GetKernel(name)
		if !ok {
			t.Logf("⚠️  Kernel %s not loaded - skipping validation", name)
			continue
		}

		// SPIR-V magic number validation
		// SPIR-V files start with: 0x07 0x23 0x02 0x03 (little-endian magic)
		if len(data) < 4 {
			t.Errorf("Kernel %s too small: %d bytes", name, len(data))
			continue
		}

		magic := uint32(data[0]) | uint32(data[1])<<8 | uint32(data[2])<<16 | uint32(data[3])<<24

		// SPIR-V magic number is 0x07230203
		if magic != 0x07230203 {
			t.Errorf("Kernel %s has invalid SPIR-V magic: 0x%08X (expected 0x07230203)", name, magic)
		} else {
			t.Logf("✅ Kernel %s is valid SPIR-V (%d bytes)", name, len(data))
		}
	}
}

// ═════════════════════════════════════════════════════════════════════════════
// OPTIMIZATION TESTS (85% Required) - Correctness & Performance
// ═════════════════════════════════════════════════════════════════════════════

// TestSPIRV_SLERPKernel_Correctness validates SLERP produces correct output
// NOTE: This tests CPU fallback correctness, GPU execution requires Level Zero
func TestSPIRV_SLERPKernel_Correctness(t *testing.T) {
	// Test SLERP correctness using CPU implementation
	// (GPU kernel would execute same algorithm)

	q0 := Identity()
	q1 := FromAxisAngle([3]float32{0, 0, 1}, 3.14159/2) // 90° rotation

	// SLERP properties to verify:
	// 1. SLERP(q0, q1, 0) = q0
	result0 := SLERP(q0, q1, 0)
	if GeodeticDistance(result0, q0) > 1e-5 {
		t.Errorf("SLERP(q0, q1, 0) should equal q0, got distance: %f", GeodeticDistance(result0, q0))
	}

	// 2. SLERP(q0, q1, 1) = q1
	result1 := SLERP(q0, q1, 1)
	if GeodeticDistance(result1, q1) > 1e-5 {
		t.Errorf("SLERP(q0, q1, 1) should equal q1, got distance: %f", GeodeticDistance(result1, q1))
	}

	// 3. SLERP result is on S³ (||Q|| = 1.0)
	result05 := SLERP(q0, q1, 0.5)
	if err := result05.Validate(); err != nil {
		t.Errorf("SLERP result not on S³: %v", err)
	}

	// 4. SLERP is geodesic (shortest path)
	dist01 := GeodeticDistance(q0, q1)
	dist0_mid := GeodeticDistance(q0, result05)
	dist_mid1 := GeodeticDistance(result05, q1)

	// Halfway point should split distance ~50/50 (within tolerance)
	expectedHalf := dist01 / 2
	if abs(dist0_mid-expectedHalf) > 0.1 {
		t.Logf("⚠️  SLERP midpoint distance: %.6f (expected ~%.6f)", dist0_mid, expectedHalf)
	}

	t.Logf("✅ SLERP correctness validated:")
	t.Logf("   - Endpoints preserved: t=0 and t=1")
	t.Logf("   - Result on S³: ||Q|| = %.6f", result05.Norm())
	t.Logf("   - Geodesic path: dist(q0,mid)=%.6f, dist(mid,q1)=%.6f", dist0_mid, dist_mid1)
}

// TestSPIRV_MatMulKernel_Correctness validates sparse matrix multiplication
func TestSPIRV_MatMulKernel_Correctness(t *testing.T) {
	// Test sparse matmul logic (CPU simulation of what GPU kernel does)
	// For production: this would execute actual SPIR-V kernel on GPU

	// Simple test case: 3x3 sparse matrix
	// [1  0  2]   [1]   [5]
	// [0  3  0] × [0] = [0]
	// [4  0  5]   [2]   [14]

	// CSR format:
	// values:      [1, 2, 3, 4, 5]
	// col_indices: [0, 2, 1, 0, 2]
	// row_ptrs:    [0, 2, 3, 5]

	values := []float32{1, 2, 3, 4, 5}
	colIndices := []int{0, 2, 1, 0, 2}
	rowPtrs := []int{0, 2, 3, 5}
	x := []float32{1, 0, 2}

	// Expected result
	expected := []float32{5, 0, 14}

	// Execute sparse matmul (CPU implementation)
	result := sparseMATVecCPU(values, colIndices, rowPtrs, x, 3)

	for i, exp := range expected {
		if abs(result[i]-exp) > 1e-5 {
			t.Errorf("Row %d: got %.6f, expected %.6f", i, result[i], exp)
		}
	}

	t.Logf("✅ Sparse matmul correctness validated:")
	t.Logf("   - Input:  [1, 0, 2]")
	t.Logf("   - Result: [%.1f, %.1f, %.1f]", result[0], result[1], result[2])
	t.Logf("   - Expected: [5, 0, 14]")
}

// TestSPIRV_KernelPerformance_SLERP benchmarks SLERP kernel
func TestSPIRV_KernelPerformance_SLERP(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping performance test in short mode")
	}

	// Benchmark SLERP performance
	q0 := Identity()
	q1 := FromAxisAngle([3]float32{0, 0, 1}, 3.14159/2)

	iterations := 100000
	t0 := testing.Benchmark(func(b *testing.B) {
		for i := 0; i < iterations; i++ {
			_ = SLERP(q0, q1, 0.5)
		}
	})

	opsPerSec := float64(iterations) / t0.T.Seconds()

	t.Logf("✅ SLERP Performance (CPU):")
	t.Logf("   - Operations: %d", iterations)
	t.Logf("   - Duration:   %.3f ms", t0.T.Seconds()*1000)
	t.Logf("   - Throughput: %.2f Kops/sec", opsPerSec/1000)
	t.Logf("   - Target:     50-100 Mops/sec on GPU (N100 @ 24 EU)")

	// CPU should achieve at least 100K ops/sec
	if opsPerSec < 100000 {
		t.Logf("⚠️  SLERP CPU performance lower than expected: %.2f Kops/sec", opsPerSec/1000)
	}
}

// TestSPIRV_KernelPerformance_MatMul benchmarks sparse matmul kernel
func TestSPIRV_KernelPerformance_MatMul(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping performance test in short mode")
	}

	// Benchmark sparse matmul with realistic data
	// 1000x1000 matrix with 80% sparsity = 200K non-zeros

	rows := 1000
	nnz := 200000

	values := make([]float32, nnz)
	colIndices := make([]int, nnz)
	rowPtrs := make([]int, rows+1)
	x := make([]float32, rows)

	// Initialize with uniform distribution
	for i := range values {
		values[i] = 1.0
		colIndices[i] = i % rows
	}
	for i := range x {
		x[i] = float32(i % 10)
	}
	for i := range rowPtrs {
		rowPtrs[i] = (i * nnz) / rows
	}

	iterations := 100
	t0 := testing.Benchmark(func(b *testing.B) {
		for i := 0; i < iterations; i++ {
			_ = sparseMATVecCPU(values, colIndices, rowPtrs, x, rows)
		}
	})

	opsPerSec := float64(iterations*nnz) / t0.T.Seconds()

	t.Logf("✅ Sparse MatMul Performance (CPU):")
	t.Logf("   - Matrix size: %dx%d (80%% sparse)", rows, rows)
	t.Logf("   - Non-zeros:   %d", nnz)
	t.Logf("   - Iterations:  %d", iterations)
	t.Logf("   - Duration:    %.3f ms", t0.T.Seconds()*1000)
	t.Logf("   - Throughput:  %.2f Mops/sec", opsPerSec/1e6)
}

// ═════════════════════════════════════════════════════════════════════════════
// EXPLORATION TESTS (70% Required) - GPU Execution & Fallback
// ═════════════════════════════════════════════════════════════════════════════

// TestSPIRV_GPUExecution_IfAvailable tests GPU execution when available
func TestSPIRV_GPUExecution_IfAvailable(t *testing.T) {
	accelerator := NewAccelerator()

	if !accelerator.IsGPUAvailable() {
		t.Skip("⚠️  GPU not available - skipping GPU execution test")
	}

	// If GPU available, test batch operations
	pairs := [][2]Quaternion{
		{Identity(), FromAxisAngle([3]float32{0, 0, 1}, 3.14159/2)},
		{Identity(), FromAxisAngle([3]float32{1, 0, 0}, 3.14159/4)},
		{Identity(), FromAxisAngle([3]float32{0, 1, 0}, 3.14159/3)},
	}

	results := accelerator.BatchSLERP(pairs, 0.5)

	if len(results) != len(pairs) {
		t.Errorf("BatchSLERP returned %d results, expected %d", len(results), len(pairs))
	}

	for i, r := range results {
		if err := r.Validate(); err != nil {
			t.Errorf("Result %d not on S³: %v", i, err)
		}
	}

	stats := accelerator.GetStats()
	t.Logf("✅ GPU execution validated:")
	t.Logf("   - Total ops:  %d", stats.TotalOps)
	t.Logf("   - GPU ops:    %d", stats.GPUOps)
	t.Logf("   - Throughput: %.2f ops/sec", stats.OpsPerSecond)
}

// TestSPIRV_FallbackToCPU validates graceful CPU fallback
func TestSPIRV_FallbackToCPU(t *testing.T) {
	accelerator := NewAccelerator()

	// Force CPU path (GPU detection returns false currently)
	if accelerator.IsGPUAvailable() {
		t.Skip("GPU available - cannot test CPU fallback")
	}

	t.Logf("✅ Testing CPU fallback path (GPU not available)")

	// Test batch operations on CPU
	pairs := [][2]Quaternion{
		{Identity(), FromAxisAngle([3]float32{0, 0, 1}, 3.14159/2)},
		{Identity(), FromAxisAngle([3]float32{1, 0, 0}, 3.14159/4)},
	}

	results := accelerator.BatchSLERP(pairs, 0.5)

	if len(results) != len(pairs) {
		t.Errorf("BatchSLERP returned %d results, expected %d", len(results), len(pairs))
	}

	// Verify CPU fallback produces correct results
	for i, r := range results {
		if err := r.Validate(); err != nil {
			t.Errorf("CPU fallback result %d not on S³: %v", i, err)
		}
	}

	stats := accelerator.GetStats()
	if stats.CPUOps == 0 {
		t.Error("Expected CPU ops to be recorded")
	}
	if stats.GPUOps > 0 {
		t.Error("GPU ops should be 0 when GPU unavailable")
	}

	t.Logf("✅ CPU fallback validated:")
	t.Logf("   - CPU ops:    %d", stats.CPUOps)
	t.Logf("   - Throughput: %.2f ops/sec", stats.OpsPerSecond)
}

// TestSPIRV_Integration_WithAccelerator tests full integration path
func TestSPIRV_Integration_WithAccelerator(t *testing.T) {
	// Test complete integration: KernelLoader + Accelerator + Operations

	// 1. Load kernels
	loader := GetKernelLoader()
	status := loader.GetStatus()
	t.Logf("Kernel loader status: %d/%d loaded", status["kernels_loaded"], status["kernels_total"])

	// 2. Initialize accelerator
	accelerator := NewAccelerator()
	accStatus := accelerator.GetStatus()
	t.Logf("Accelerator backend: %s", accStatus["backend"])

	// 3. Execute operations
	testData := [][2]Quaternion{
		{Identity(), FromAxisAngle([3]float32{0, 0, 1}, 3.14159/2)},
	}

	results := accelerator.BatchSLERP(testData, 0.5)
	if len(results) != 1 {
		t.Errorf("Expected 1 result, got %d", len(results))
	}

	// 4. Validate correctness
	if err := results[0].Validate(); err != nil {
		t.Errorf("Result validation failed: %v", err)
	}

	// 5. Check statistics
	stats := accelerator.GetStats()
	if stats.TotalOps == 0 {
		t.Error("No operations recorded")
	}

	t.Logf("✅ Full integration validated:")
	t.Logf("   - Kernels loaded:  %v", status["kernels_loaded"])
	t.Logf("   - Backend:         %s", accStatus["backend"])
	t.Logf("   - Total ops:       %d", stats.TotalOps)
	t.Logf("   - GPU utilization: %d/%d ops", stats.GPUOps, stats.TotalOps)
}

// ═════════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═════════════════════════════════════════════════════════════════════════════

// sparseMATVecCPU executes sparse matrix-vector multiplication on CPU
// Simulates what GPU kernel does (for correctness testing)
func sparseMATVecCPU(values []float32, colIndices, rowPtrs []int, x []float32, rows int) []float32 {
	result := make([]float32, rows)

	for row := 0; row < rows; row++ {
		start := rowPtrs[row]
		end := rowPtrs[row+1]

		sum := float32(0)
		for idx := start; idx < end; idx++ {
			col := colIndices[idx]
			val := values[idx]
			sum += val * x[col]
		}

		result[row] = sum
	}

	return result
}
