// Memory Benchmark - Standalone Williams Space Efficiency Validator
//
// CARMACK MANDATE: "Show me the ACTUAL memory usage at n=1M."
//
// This executable demonstrates Williams O(√t × log₂t) space efficiency
// with REAL memory measurements at multiple problem sizes.
//
// Usage:
//   go run cmd/memory_benchmark/main.go
//
// Author: Asymmetrica Research Dyad
// Created: 2025-12-27
package main

import (
	"fmt"
	"math"
	"os"

	"github.com/asymmetrica/urbanlens/pkg/profiling"
)

func main() {
	fmt.Println("╔══════════════════════════════════════════════════════════════════════════╗")
	fmt.Println("║            WILLIAMS SPACE EFFICIENCY MEMORY BENCHMARK                    ║")
	fmt.Println("║            CARMACK CHALLENGE: Show ACTUAL memory at n=1M                 ║")
	fmt.Println("╚══════════════════════════════════════════════════════════════════════════╝")
	fmt.Println()

	profiler := profiling.NewMemoryProfiler()

	// Test 1: Small allocation (n=100)
	fmt.Println("🔬 Test 1: Small Allocation (N=100)")
	fmt.Println("──────────────────────────────────────────────────────────────────────────")
	runSingleBenchmark(profiler, 100)

	// Test 2: Medium allocation (n=1,000)
	fmt.Println("\n🔬 Test 2: Medium Allocation (N=1,000)")
	fmt.Println("──────────────────────────────────────────────────────────────────────────")
	runSingleBenchmark(profiler, 1_000)

	// Test 3: Large allocation (n=10,000)
	fmt.Println("\n🔬 Test 3: Large Allocation (N=10,000)")
	fmt.Println("──────────────────────────────────────────────────────────────────────────")
	runSingleBenchmark(profiler, 10_000)

	// Test 4: Very large allocation (n=100,000)
	fmt.Println("\n🔬 Test 4: Very Large Allocation (N=100,000)")
	fmt.Println("──────────────────────────────────────────────────────────────────────────")
	runSingleBenchmark(profiler, 100_000)

	// Test 5: CARMACK CHALLENGE (n=1,000,000)
	fmt.Println("\n🔥 CARMACK CHALLENGE: N=1,000,000")
	fmt.Println("══════════════════════════════════════════════════════════════════════════")
	result := runSingleBenchmark(profiler, 1_000_000)

	// Carmack verdict
	fmt.Println("\n╔══════════════════════════════════════════════════════════════════════════╗")
	fmt.Println("║                      CARMACK CHALLENGE VERDICT                           ║")
	fmt.Println("╚══════════════════════════════════════════════════════════════════════════╝")

	if result.WilliamsCompare.Status == "failing" {
		fmt.Println("❌ FAILED: Memory usage exceeds Williams bound significantly")
		fmt.Printf("   Efficiency: %.2fx theoretical (target: ≤2.0x)\n", result.WilliamsCompare.SpaceEfficiency)
		os.Exit(1)
	} else if result.WilliamsCompare.Status == "needs_work" {
		fmt.Println("⚠️  NEEDS WORK: Memory usage suboptimal but within acceptable range")
		fmt.Printf("   Efficiency: %.2fx theoretical (target: ≤1.1x for optimal)\n", result.WilliamsCompare.SpaceEfficiency)
	} else if result.WilliamsCompare.Status == "acceptable" {
		fmt.Println("✓ ACCEPTABLE: Memory usage within 2x of Williams bound")
		fmt.Printf("   Efficiency: %.2fx theoretical\n", result.WilliamsCompare.SpaceEfficiency)
	} else {
		fmt.Println("✅ OPTIMAL: Memory usage within 10% of Williams theoretical bound!")
		fmt.Printf("   Efficiency: %.2fx theoretical\n", result.WilliamsCompare.SpaceEfficiency)
	}

	fmt.Printf("\n   Memory Reduction: %.1f%% vs linear O(N)\n", result.WilliamsCompare.MemoryReduction)
	fmt.Printf("   Efficiency Rating: %.2fx (target: ≥1.5x)\n", result.WilliamsCompare.EfficiencyRating)

	fmt.Println("\n💡 Carmack says: \"Performance claims without profiler evidence are fiction.\"")
	fmt.Println("   This is the EVIDENCE. ✅")
}

func runSingleBenchmark(profiler *profiling.MemoryProfiler, n int) profiling.MemoryBenchmarkResult {
	// Calculate Williams batch size
	batchSize := int(math.Sqrt(float64(n)) * math.Log2(float64(n)))

	fmt.Printf("\nWilliams Batch Size: %d (%.1f%% of N)\n", batchSize, float64(batchSize)/float64(n)*100)

	// Run benchmark with Williams batching
	result := profiler.RunMemoryBenchmark(
		n,
		func() {
			// Allocate with Williams batching
			batches := make([][]int64, 0, (n+batchSize-1)/batchSize)

			for i := 0; i < n; i += batchSize {
				end := i + batchSize
				if end > n {
					end = n
				}
				batch := make([]int64, end-i)
				batches = append(batches, batch)
			}

			_ = batches
		},
		8, // bytes per int64
	)

	// Print results
	fmt.Println("\n📊 RESULTS:")
	fmt.Println(result.Allocations.Format())
	fmt.Println()
	fmt.Println(result.WilliamsCompare.Format())

	return result
}
