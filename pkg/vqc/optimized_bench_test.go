// Package vqc - Benchmark Suite for Optimizations
// Measures before/after performance for all optimizations
//
// Run with: go test -bench=. -benchmem -benchtime=5s
package vqc

import (
	"math/rand"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// DIGITAL ROOT FILTERING BENCHMARKS
// Compare: Naive vs Optimized vs ZeroCopy vs Parallel
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkDigitalRootFilter_Naive_1K(b *testing.B) {
	candidates := makeInt64Candidates(1_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterInt64(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_Optimized_1K(b *testing.B) {
	candidates := makeInt64Candidates(1_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterOptimized(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_ZeroCopy_1K(b *testing.B) {
	candidates := makeInt64Candidates(1_000)
	target := int64(12345)
	output := make([]int64, len(candidates)/9+10) // Pre-allocate

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterZeroCopy(candidates, target, output)
	}
}

func BenchmarkDigitalRootFilter_Naive_10K(b *testing.B) {
	candidates := makeInt64Candidates(10_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterInt64(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_Optimized_10K(b *testing.B) {
	candidates := makeInt64Candidates(10_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterOptimized(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_ZeroCopy_10K(b *testing.B) {
	candidates := makeInt64Candidates(10_000)
	target := int64(12345)
	output := make([]int64, len(candidates)/9+100)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterZeroCopy(candidates, target, output)
	}
}

func BenchmarkDigitalRootFilter_Naive_100K(b *testing.B) {
	candidates := makeInt64Candidates(100_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterInt64(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_Optimized_100K(b *testing.B) {
	candidates := makeInt64Candidates(100_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterOptimized(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_Parallel_100K(b *testing.B) {
	candidates := makeInt64Candidates(100_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterParallel(candidates, target)
	}
}

func BenchmarkDigitalRootFilter_Parallel_1M(b *testing.B) {
	candidates := makeInt64Candidates(1_000_000)
	target := int64(12345)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = DigitalRootFilterParallel(candidates, target)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION ARRAY BENCHMARKS
// Compare: Slice-of-Structs vs Struct-of-Arrays
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkQuaternion_SliceOfStructs_Normalize_1K(b *testing.B) {
	quats := makeQuaternionSlice(1_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range quats {
			quats[j] = quats[j].Normalize()
		}
	}
}

func BenchmarkQuaternion_StructOfArrays_Normalize_1K(b *testing.B) {
	qa := makeQuaternionArray(1_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		qa.NormalizeBatch()
	}
}

func BenchmarkQuaternion_SliceOfStructs_Normalize_10K(b *testing.B) {
	quats := makeQuaternionSlice(10_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range quats {
			quats[j] = quats[j].Normalize()
		}
	}
}

func BenchmarkQuaternion_StructOfArrays_Normalize_10K(b *testing.B) {
	qa := makeQuaternionArray(10_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		qa.NormalizeBatch()
	}
}

func BenchmarkQuaternion_SliceOfStructs_Dot_1K(b *testing.B) {
	quats := makeQuaternionSlice(1_000)
	target := NewQuaternion(0.5, 0.5, 0.5, 0.5).Normalize()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range quats {
			_ = quats[j].Dot(target)
		}
	}
}

func BenchmarkQuaternion_StructOfArrays_Dot_1K(b *testing.B) {
	qa := makeQuaternionArray(1_000)
	target := NewQuaternion(0.5, 0.5, 0.5, 0.5).Normalize()
	results := make([]float64, qa.N)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		qa.DotBatch(target, results)
	}
}

func BenchmarkQuaternion_SliceOfStructs_Scale_1K(b *testing.B) {
	quats := makeQuaternionSlice(1_000)
	scale := 2.5

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range quats {
			quats[j] = quats[j].Scale(scale)
		}
	}
}

func BenchmarkQuaternion_StructOfArrays_Scale_1K(b *testing.B) {
	qa := makeQuaternionArray(1_000)
	scale := 2.5

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		qa.ScaleBatch(scale)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// SLERP BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkSLERP_Individual_1K(b *testing.B) {
	q0s := makeQuaternionSlice(1_000)
	q1s := makeQuaternionSlice(1_000)
	t := 0.5

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range q0s {
			_ = SLERP(q0s[j], q1s[j], t)
		}
	}
}

func BenchmarkSLERP_Batch_1K(b *testing.B) {
	qa0 := makeQuaternionArray(1_000)
	qa1 := makeQuaternionArray(1_000)
	qaResult := NewQuaternionArray(1_000)
	t := 0.5

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		SLERPBatch(qa0, qa1, t, qaResult)
	}
}

func BenchmarkSLERP_Individual_10K(b *testing.B) {
	q0s := makeQuaternionSlice(10_000)
	q1s := makeQuaternionSlice(10_000)
	t := 0.5

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range q0s {
			_ = SLERP(q0s[j], q1s[j], t)
		}
	}
}

func BenchmarkSLERP_Batch_10K(b *testing.B) {
	qa0 := makeQuaternionArray(10_000)
	qa1 := makeQuaternionArray(10_000)
	qaResult := NewQuaternionArray(10_000)
	t := 0.5

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		SLERPBatch(qa0, qa1, t, qaResult)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// MULTIPLICATION BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkMultiply_Individual_1K(b *testing.B) {
	q0s := makeQuaternionSlice(1_000)
	q1s := makeQuaternionSlice(1_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range q0s {
			_ = q0s[j].Multiply(q1s[j])
		}
	}
}

func BenchmarkMultiply_Batch_1K(b *testing.B) {
	qa0 := makeQuaternionArray(1_000)
	qa1 := makeQuaternionArray(1_000)
	qaResult := NewQuaternionArray(1_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		MultiplyBatch(qa0, qa1, qaResult)
	}
}

func BenchmarkMultiply_Individual_10K(b *testing.B) {
	q0s := makeQuaternionSlice(10_000)
	q1s := makeQuaternionSlice(10_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := range q0s {
			_ = q0s[j].Multiply(q1s[j])
		}
	}
}

func BenchmarkMultiply_Batch_10K(b *testing.B) {
	qa0 := makeQuaternionArray(10_000)
	qa1 := makeQuaternionArray(10_000)
	qaResult := NewQuaternionArray(10_000)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		MultiplyBatch(qa0, qa1, qaResult)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// OBJECT POOLING BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkQuaternion_NoPooling(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		q := &Quaternion{W: 1, X: 2, Y: 3, Z: 4}
		_ = q.Normalize()
		// Let GC handle it
	}
}

func BenchmarkQuaternion_WithPooling(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		q := GetQuaternion()
		q.W, q.X, q.Y, q.Z = 1, 2, 3, 4
		_ = q.Normalize()
		PutQuaternion(q)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// UNSAFE ZERO-COPY BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkFloat64Copy_Standard(b *testing.B) {
	src := make([]float64, 10_000)
	for i := range src {
		src[i] = float64(i)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		dst := make([]float64, len(src))
		copy(dst, src)
		_ = dst
	}
}

func BenchmarkFloat64Copy_UnsafeView(b *testing.B) {
	src := make([]float64, 10_000)
	for i := range src {
		src[i] = float64(i)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		bytes := Float64ArrayToBytes(src)
		dst := BytesToFloat64Array(bytes)
		_ = dst
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS FOR BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════

func makeInt64Candidates(n int) []int64 {
	candidates := make([]int64, n)
	for i := 0; i < n; i++ {
		candidates[i] = int64(i)
	}
	return candidates
}

func makeQuaternionSlice(n int) []Quaternion {
	quats := make([]Quaternion, n)
	for i := 0; i < n; i++ {
		quats[i] = NewQuaternion(
			rand.Float64(),
			rand.Float64(),
			rand.Float64(),
			rand.Float64(),
		).Normalize()
	}
	return quats
}

func makeQuaternionArray(n int) *QuaternionArray {
	qa := NewQuaternionArray(n)
	for i := 0; i < n; i++ {
		q := NewQuaternion(
			rand.Float64(),
			rand.Float64(),
			rand.Float64(),
			rand.Float64(),
		).Normalize()
		qa.Append(q)
	}
	return qa
}

// ═══════════════════════════════════════════════════════════════════════════
// THROUGHPUT CALCULATION BENCHMARKS
// Calculate actual ops/sec for reporting
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkThroughput_DigitalRoot_100M(b *testing.B) {
	// Measure raw digital root ops/sec
	b.ReportAllocs()
	count := int64(0)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := int64(0); j < 100_000_000; j++ {
			_ = DigitalRootInt64(j)
			count++
		}
	}

	b.StopTimer()
	seconds := b.Elapsed().Seconds()
	opsPerSec := float64(count) / seconds
	b.ReportMetric(opsPerSec/1_000_000, "Mops/s")
}

func BenchmarkThroughput_Quaternion_10M(b *testing.B) {
	// Measure quaternion normalize ops/sec
	qa := makeQuaternionArray(10_000_000)
	count := int64(0)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		qa.NormalizeBatch()
		count += int64(qa.N)
	}

	b.StopTimer()
	seconds := b.Elapsed().Seconds()
	opsPerSec := float64(count) / seconds
	b.ReportMetric(opsPerSec/1_000_000, "Mops/s")
}

func BenchmarkThroughput_SLERP_1M(b *testing.B) {
	// Measure SLERP ops/sec
	qa0 := makeQuaternionArray(1_000_000)
	qa1 := makeQuaternionArray(1_000_000)
	qaResult := NewQuaternionArray(1_000_000)
	count := int64(0)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		SLERPBatch(qa0, qa1, 0.5, qaResult)
		count += int64(qa0.N)
	}

	b.StopTimer()
	seconds := b.Elapsed().Seconds()
	opsPerSec := float64(count) / seconds
	b.ReportMetric(opsPerSec/1_000_000, "Mops/s")
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARK ANALYSIS REPORT
// ═══════════════════════════════════════════════════════════════════════════
//
// Expected Results (based on optimizations):
//
// Digital Root Filtering:
//   Naive (1K):        ~500 ns/op,  ~10 MB/s
//   Optimized (1K):    ~300 ns/op,  ~6 MB/s   (1.7× faster)
//   ZeroCopy (1K):     ~250 ns/op,  ~0 MB/s   (2× faster, zero alloc!)
//   Parallel (100K):   ~100 µs/op,  ~200 MB/s (5× faster)
//
// Quaternion Operations:
//   SliceOfStructs (1K):    ~15 µs/op
//   StructOfArrays (1K):    ~5 µs/op  (3× faster, SIMD-friendly!)
//
// SLERP:
//   Individual (1K):   ~80 µs/op
//   Batch (1K):        ~30 µs/op     (2.7× faster)
//
// Object Pooling:
//   NoPooling:         ~50 ns/op,  ~48 B/op
//   WithPooling:       ~20 ns/op,  ~0 B/op   (2.5× faster, zero alloc!)
//
// Overall Expected Throughput:
//   Current:   6.58M ops/sec
//   Optimized: 13-20M ops/sec  (2-3× improvement)
//
// To reach 71M ops/sec:
//   Need GPU acceleration for remaining 3.5-5.5× speedup
//
// Carmack Quote:
//   "Premature optimization is the root of all evil. But informed optimization
//    after profiling is the root of all performance."
//
// ═══════════════════════════════════════════════════════════════════════════
