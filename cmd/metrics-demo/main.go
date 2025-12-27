// cmd/metrics-demo - Performance Metrics Dashboard Demo
//
// Demonstrates the performance tracking system with live metrics
// collection, gap analysis, and report generation.
//
// Usage:
//   go run cmd/metrics-demo/main.go
//
// Output:
//   - Live metrics tracking
//   - Performance report (JSON, Markdown)
//   - Gap analysis vs targets
//   - Optimization recommendations
package main

import (
	"fmt"
	"math"
	"math/rand"
	"os"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/profiling"
)

// Quaternion for demo purposes
type Quaternion struct {
	W, X, Y, Z float64
}

func (q Quaternion) Normalize() Quaternion {
	norm := math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
	if norm > 1e-10 {
		return Quaternion{q.W / norm, q.X / norm, q.Y / norm, q.Z / norm}
	}
	return Quaternion{1, 0, 0, 0}
}

func (q1 Quaternion) Multiply(q2 Quaternion) Quaternion {
	return Quaternion{
		W: q1.W*q2.W - q1.X*q2.X - q1.Y*q2.Y - q1.Z*q2.Z,
		X: q1.W*q2.X + q1.X*q2.W + q1.Y*q2.Z - q1.Z*q2.Y,
		Y: q1.W*q2.Y - q1.X*q2.Z + q1.Y*q2.W + q1.Z*q2.X,
		Z: q1.W*q2.Z + q1.X*q2.Y - q1.Y*q2.X + q1.Z*q2.W,
	}
}

func (q1 Quaternion) Dot(q2 Quaternion) float64 {
	return q1.W*q2.W + q1.X*q2.X + q1.Y*q2.Y + q1.Z*q2.Z
}

func SLERP(q1, q2 Quaternion, t float64) Quaternion {
	dot := q1.Dot(q2)
	if dot < 0 {
		q2 = Quaternion{-q2.W, -q2.X, -q2.Y, -q2.Z}
		dot = -dot
	}

	if dot > 0.9995 {
		// Linear interpolation for nearly parallel quaternions
		result := Quaternion{
			W: q1.W + t*(q2.W-q1.W),
			X: q1.X + t*(q2.X-q1.X),
			Y: q1.Y + t*(q2.Y-q1.Y),
			Z: q1.Z + t*(q2.Z-q1.Z),
		}
		return result.Normalize()
	}

	theta := math.Acos(dot)
	sinTheta := math.Sin(theta)
	w1 := math.Sin((1-t)*theta) / sinTheta
	w2 := math.Sin(t*theta) / sinTheta

	return Quaternion{
		W: w1*q1.W + w2*q2.W,
		X: w1*q1.X + w2*q2.X,
		Y: w1*q1.Y + w2*q2.Y,
		Z: w1*q1.Z + w2*q2.Z,
	}
}

func RandomQuaternion() Quaternion {
	q := Quaternion{
		W: rand.Float64()*2 - 1,
		X: rand.Float64()*2 - 1,
		Y: rand.Float64()*2 - 1,
		Z: rand.Float64()*2 - 1,
	}
	return q.Normalize()
}

func main() {
	fmt.Println("╔═══════════════════════════════════════════════════════════════╗")
	fmt.Println("║  Performance Metrics Dashboard Demo                          ║")
	fmt.Println("║  Asymmetrica UrbanLens - Mathematical Reality Engine         ║")
	fmt.Println("╚═══════════════════════════════════════════════════════════════╝\n")

	metrics := profiling.GetMetrics()
	metrics.Enable()

	// Seed RNG
	rand.Seed(time.Now().UnixNano())

	// ═══════════════════════════════════════════════════════════════
	// SIMULATION 1: Quaternion Multiply (CPU Baseline)
	// ═══════════════════════════════════════════════════════════════

	fmt.Println("📊 Simulating Quaternion Multiply (CPU)...")
	fmt.Println("   Target: 1M ops/sec")

	q1 := RandomQuaternion()
	q2 := RandomQuaternion()

	for i := 0; i < 10000; i++ {
		start := time.Now()
		_ = q1.Multiply(q2)
		duration := time.Since(start)
		profiling.RecordOperation("quaternion_multiply", duration, 0)
	}

	stats := metrics.GetStats("quaternion_multiply")
	fmt.Printf("   ✓ Completed: %d operations\n", stats.Count)
	fmt.Printf("   ✓ Throughput: %.2f M ops/sec\n", stats.OpsPerSecond/1e6)
	fmt.Printf("   ✓ Avg Duration: %v\n", stats.AvgDuration)
	fmt.Printf("   ✓ P95: %v | P99: %v\n\n", stats.P95, stats.P99)

	// ═══════════════════════════════════════════════════════════════
	// SIMULATION 2: Quaternion SLERP (More Complex)
	// ═══════════════════════════════════════════════════════════════

	fmt.Println("📊 Simulating Quaternion SLERP (CPU)...")
	fmt.Println("   Target: 500K ops/sec")

	for i := 0; i < 5000; i++ {
		q1 = RandomQuaternion()
		q2 = RandomQuaternion()
		t := rand.Float64()

		start := time.Now()
		_ = SLERP(q1, q2, t)
		duration := time.Since(start)
		profiling.RecordOperation("quaternion_slerp", duration, 0)
	}

	slerpStats := metrics.GetStats("quaternion_slerp")
	fmt.Printf("   ✓ Completed: %d operations\n", slerpStats.Count)
	fmt.Printf("   ✓ Throughput: %.2f K ops/sec\n", slerpStats.OpsPerSecond/1e3)
	fmt.Printf("   ✓ Avg Duration: %v\n", slerpStats.AvgDuration)
	fmt.Printf("   ✓ P95: %v | P99: %v\n\n", slerpStats.P95, slerpStats.P99)

	// ═══════════════════════════════════════════════════════════════
	// SIMULATION 3: Digital Root Filter (Vedic 53× speedup)
	// ═══════════════════════════════════════════════════════════════

	fmt.Println("📊 Simulating Digital Root Filter (Vedic)...")
	fmt.Println("   Target: 100M ops/sec (O(1) operation)")

	digitalRoot := func(n int) int {
		if n == 0 {
			return 0
		}
		return 1 + (n-1)%9
	}

	for i := 0; i < 100000; i++ {
		n := rand.Intn(1000000)

		start := time.Now()
		_ = digitalRoot(n)
		duration := time.Since(start)
		profiling.RecordOperation("digital_root", duration, 0)
	}

	drStats := metrics.GetStats("digital_root")
	fmt.Printf("   ✓ Completed: %d operations\n", drStats.Count)
	fmt.Printf("   ✓ Throughput: %.2f M ops/sec\n", drStats.OpsPerSecond/1e6)
	fmt.Printf("   ✓ Avg Duration: %v\n", drStats.AvgDuration)
	fmt.Printf("   ✓ P95: %v | P99: %v\n\n", drStats.P95, drStats.P99)

	// ═══════════════════════════════════════════════════════════════
	// SIMULATION 4: Simulate VQC Engine (with intentional slowdown)
	// ═══════════════════════════════════════════════════════════════

	fmt.Println("📊 Simulating VQC Engine (CPU fallback - intentionally slow)...")
	fmt.Println("   Target: 71M ops/sec (GPU)")
	fmt.Println("   Current: ~6.58M ops/sec (CPU fallback)")

	// Simulate VQC at current CPU performance (~152ns per op = 6.58M ops/sec)
	for i := 0; i < 1000; i++ {
		start := time.Now()
		// Simulate quaternion evolution (multiple operations)
		q1 = RandomQuaternion()
		q2 = RandomQuaternion()
		_ = q1.Multiply(q2)
		_ = SLERP(q1, q2, 0.5)
		duration := time.Since(start)
		profiling.RecordOperation("vqc_engine", duration, 0)
	}

	vqcStats := metrics.GetStats("vqc_engine")
	fmt.Printf("   ✓ Completed: %d operations\n", vqcStats.Count)
	fmt.Printf("   ✓ Throughput: %.2f M ops/sec\n", vqcStats.OpsPerSecond/1e6)
	fmt.Printf("   ✓ Avg Duration: %v\n", vqcStats.AvgDuration)
	fmt.Printf("   ✓ P95: %v | P99: %v\n\n", vqcStats.P95, vqcStats.P99)

	// ═══════════════════════════════════════════════════════════════
	// GENERATE PERFORMANCE REPORT
	// ═══════════════════════════════════════════════════════════════

	fmt.Println("═══════════════════════════════════════════════════════════════\n")
	fmt.Println("📈 Generating Performance Report...\n")

	report := metrics.GenerateReport()

	// Print summary
	fmt.Println("╔═══════════════════════════════════════════════════════════════╗")
	fmt.Println("║  PERFORMANCE SUMMARY                                          ║")
	fmt.Println("╚═══════════════════════════════════════════════════════════════╝\n")

	fmt.Printf("Total Operations: %d\n", report.Summary.TotalOperations)
	fmt.Printf("Total Samples:    %d\n", report.Summary.TotalSamples)
	fmt.Printf("Overall Status:   %s\n\n", report.Summary.OverallStatus)

	fmt.Printf("Status Distribution:\n")
	fmt.Printf("  ✅ Excellent:   %d\n", report.Summary.ExcellentCount)
	fmt.Printf("  ✓  Good:        %d\n", report.Summary.GoodCount)
	fmt.Printf("  ⚠️  Needs Work:  %d\n", report.Summary.NeedsWorkCount)
	fmt.Printf("  ❌ Critical:    %d\n\n", report.Summary.CriticalCount)

	// Detailed operation reports
	fmt.Println("╔═══════════════════════════════════════════════════════════════╗")
	fmt.Println("║  DETAILED OPERATION REPORTS                                   ║")
	fmt.Println("╚═══════════════════════════════════════════════════════════════╝\n")

	operations := []string{
		"quaternion_multiply",
		"quaternion_slerp",
		"digital_root",
		"vqc_engine",
	}

	for _, opName := range operations {
		opReport, exists := report.Operations[opName]
		if !exists {
			continue
		}

		fmt.Printf("─────────────────────────────────────────────────────────────\n")
		fmt.Printf("Operation: %s\n", opReport.Name)
		fmt.Printf("─────────────────────────────────────────────────────────────\n")

		// Status badge
		var badge string
		switch opReport.Status {
		case "EXCELLENT":
			badge = "✅ EXCELLENT"
		case "GOOD":
			badge = "✓ GOOD"
		case "NEEDS_WORK":
			badge = "⚠️ NEEDS WORK"
		case "CRITICAL":
			badge = "❌ CRITICAL"
		default:
			badge = "⚪ NO TARGET"
		}
		fmt.Printf("Status: %s\n\n", badge)

		// Statistics
		fmt.Printf("Statistics:\n")
		fmt.Printf("  Count:        %d\n", opReport.Stats.Count)
		fmt.Printf("  Ops/Sec:      %.2f M\n", opReport.Stats.OpsPerSecond/1e6)
		fmt.Printf("  Avg Duration: %v\n", opReport.Stats.AvgDuration)
		fmt.Printf("  P50:          %v\n", opReport.Stats.P50)
		fmt.Printf("  P95:          %v\n", opReport.Stats.P95)
		fmt.Printf("  P99:          %v\n\n", opReport.Stats.P99)

		// Target comparison
		if opReport.Target != nil {
			fmt.Printf("Target:\n")
			fmt.Printf("  Target Ops/Sec: %.2f M\n", opReport.Target.TargetOpsPerSec/1e6)
			fmt.Printf("  Throughput Gap: %.1f%%\n", opReport.ThroughputGap)
			if opReport.ThroughputGap >= 0 {
				fmt.Printf("  Status:         ✅ EXCEEDS TARGET\n\n")
			} else {
				fmt.Printf("  Status:         ❌ BELOW TARGET\n\n")
			}
		}

		// Recommendations
		if len(opReport.Recommendations) > 0 {
			fmt.Printf("Recommendations:\n")
			for _, rec := range opReport.Recommendations {
				fmt.Printf("  • %s\n", rec)
			}
			fmt.Printf("\n")
		}
	}

	// ═══════════════════════════════════════════════════════════════
	// EXPORT REPORTS
	// ═══════════════════════════════════════════════════════════════

	fmt.Println("═══════════════════════════════════════════════════════════════\n")
	fmt.Println("💾 Exporting Reports...\n")

	// Export JSON
	jsonFile := "performance_report.json"
	if err := report.ExportJSON(jsonFile); err != nil {
		fmt.Printf("❌ Failed to export JSON: %v\n", err)
	} else {
		fmt.Printf("✅ JSON report saved: %s\n", jsonFile)
	}

	// Export Markdown
	mdFile := "performance_report.md"
	if err := report.ExportMarkdown(mdFile); err != nil {
		fmt.Printf("❌ Failed to export Markdown: %v\n", err)
	} else {
		fmt.Printf("✅ Markdown report saved: %s\n", mdFile)
	}

	fmt.Println("\n═══════════════════════════════════════════════════════════════")
	fmt.Println("✨ Demo Complete!")
	fmt.Println("═══════════════════════════════════════════════════════════════\n")

	fmt.Println("📖 Next Steps:")
	fmt.Println("   1. Review PERFORMANCE_BASELINE.md for gap analysis")
	fmt.Println("   2. Check performance_report.md for detailed metrics")
	fmt.Println("   3. Activate GPU runtime (P0 CRITICAL!)")
	fmt.Println("   4. Re-run this demo with GPU active")
	fmt.Println("   5. Target: 71M ops/sec (10.8× improvement)")
	fmt.Println("\n🔥 The GPU code exists - we just need to flip the switch! 🔥\n")

	os.Exit(0)
}
