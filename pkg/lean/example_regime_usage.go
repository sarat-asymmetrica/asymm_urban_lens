// +build ignore

package main

import (
	"fmt"
	"math"

	"github.com/asymmetrica/urbanlens/pkg/lean"
)

func main() {
	fmt.Println("╔═══════════════════════════════════════════════════════════════════╗")
	fmt.Println("║       THREE-REGIME DERIVATION - USAGE EXAMPLE                     ║")
	fmt.Println("╚═══════════════════════════════════════════════════════════════════╝")
	fmt.Println()

	// Create the theorem
	theorem := lean.NewThreeRegimeTheorem()

	// Get optimal ratios
	r1, r2, r3 := theorem.GetOptimalRatios()
	fmt.Printf("OPTIMAL REGIME DISTRIBUTION:\n")
	fmt.Printf("  R1 (Exploration):   %.2f%% (%.2f)\n", r1*100, r1)
	fmt.Printf("  R2 (Optimization):  %.2f%% (%.2f) ← THE BOTTLENECK!\n", r2*100, r2)
	fmt.Printf("  R3 (Stabilization): %.2f%% (%.2f) ← THE MAJORITY!\n", r3*100, r3)
	fmt.Printf("  Sum: %.10f (should be 1.0)\n", r1+r2+r3)
	fmt.Println()

	// Show cost coefficients
	fmt.Println("COMPUTATIONAL COST COEFFICIENTS:")
	fmt.Printf("  k1 (Exploration):   %.1f  [O(n²) operations]\n", theorem.K1_ExplorationCost)
	fmt.Printf("  k2 (Optimization):  %.1f  [O(n log n) operations] ← MOST EXPENSIVE!\n", theorem.K2_OptimizationCost)
	fmt.Printf("  k3 (Stabilization): %.1f  [O(n) operations] ← CHEAPEST!\n", theorem.K3_StabilizationCost)
	fmt.Println()

	// Show energy levels
	fmt.Println("ENERGY LEVELS (Boltzmann distribution):")
	fmt.Printf("  E1 (Exploration):   %.1f  [moderate energy]\n", theorem.E1_ExplorationEnergy)
	fmt.Printf("  E2 (Optimization):  %.1f  [HIGHEST energy - smallest regime!]\n", theorem.E2_OptimizationEnergy)
	fmt.Printf("  E3 (Stabilization): %.1f  [LOWEST energy - largest regime!]\n", theorem.E3_StabilizationEnergy)
	fmt.Println()

	// Compute entropy
	entropy := theorem.ComputeEntropy(r1, r2, r3)
	fmt.Printf("SHANNON ENTROPY: %.4f bits\n", entropy)
	fmt.Println()

	// Compute total cost for various problem sizes
	fmt.Println("TOTAL COMPUTATIONAL COST (by problem size):")
	for _, n := range []int{100, 1000, 10000, 100000} {
		cost := theorem.ComputeTotalCost(r1, r2, r3, n)
		fmt.Printf("  n=%6d: %15.2f units\n", n, cost)
	}
	fmt.Println()

	// Compute free energy
	freeEnergy := theorem.ComputeFreeEnergy(r1, r2, r3)
	fmt.Printf("FREE ENERGY: F = E - T×S = %.4f units\n", freeEnergy)
	fmt.Println()

	// Check stability
	fmt.Printf("STABILITY CHECK: R3 ≥ 50%% → %v (prevents singularities!)\n",
		theorem.IsStable(r1, r2, r3))
	fmt.Println()

	// Compare to other distributions
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println("COMPARISON WITH OTHER DISTRIBUTIONS:")
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println()

	distributions := []struct {
		name string
		r1   float64
		r2   float64
		r3   float64
	}{
		{"Optimal [30,20,50]", 0.30, 0.20, 0.50},
		{"Uniform [33,33,33]", 0.333, 0.333, 0.334},
		{"Exploration-heavy [50,25,25]", 0.50, 0.25, 0.25},
		{"Stabilization-heavy [20,20,60]", 0.20, 0.20, 0.60},
		{"Insufficient R2 [35,10,55]", 0.35, 0.10, 0.55},
		{"Insufficient R3 [40,30,30]", 0.40, 0.30, 0.30},
	}

	fmt.Printf("%-30s | %8s | %8s | %8s | %10s | %8s\n",
		"Distribution", "Entropy", "Cost", "Free E", "Distance", "Stable?")
	fmt.Println("───────────────────────────────┼──────────┼──────────┼──────────┼──────────┼─────────")

	for _, dist := range distributions {
		entropy := theorem.ComputeEntropy(dist.r1, dist.r2, dist.r3)
		cost := theorem.ComputeTotalCost(dist.r1, dist.r2, dist.r3, 1000)
		freeE := theorem.ComputeFreeEnergy(dist.r1, dist.r2, dist.r3)
		distance := theorem.ComputeDistanceFromOptimal(dist.r1, dist.r2, dist.r3)
		stable := theorem.IsStable(dist.r1, dist.r2, dist.r3)

		stableStr := "❌"
		if stable {
			stableStr = "✅"
		}

		fmt.Printf("%-30s | %8.4f | %8.0f | %8.4f | %8.4f | %6s\n",
			dist.name, entropy, cost, freeE, distance, stableStr)
	}
	fmt.Println()

	// Regime classification examples
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println("REGIME CLASSIFICATION EXAMPLES:")
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println()

	scenarios := []struct {
		name     string
		entropy  float64
		gradient float64
		stability float64
	}{
		{"Early exploration", 0.85, 0.20, 0.15},
		{"Focused optimization", 0.40, 0.75, 0.30},
		{"Final stabilization", 0.20, 0.30, 0.90},
		{"Unclear case", 0.45, 0.45, 0.45},
	}

	for _, scenario := range scenarios {
		phase := theorem.ValidateRegimeTransition(scenario.entropy, scenario.gradient, scenario.stability)
		fmt.Printf("%-25s → %s\n", scenario.name, phase)
		fmt.Printf("  (entropy=%.2f, gradient=%.2f, stability=%.2f)\n",
			scenario.entropy, scenario.gradient, scenario.stability)
	}
	fmt.Println()

	// Time series classification
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println("TIME SERIES CLASSIFICATION:")
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println()

	// Simulate three different time series
	highVarianceSeries := []float64{10, 5, 15, 2, 18, 8, 20, 1, 12, 16, 6, 19, 3, 17}
	mediumVarianceSeries := []float64{10, 11, 9, 12, 8, 11, 10, 12, 9, 11, 10, 11, 9, 12}
	lowVarianceSeries := []float64{10.0, 10.1, 9.9, 10.2, 9.8, 10.1, 10.0, 9.9, 10.1, 10.0, 10.1, 9.9, 10.0, 10.1}

	seriesList := []struct {
		name   string
		values []float64
	}{
		{"High variance (exploration)", highVarianceSeries},
		{"Medium variance (optimization)", mediumVarianceSeries},
		{"Low variance (stabilization)", lowVarianceSeries},
	}

	for _, series := range seriesList {
		phase, variance := lean.EstimateRegimeFromHistory(series.values, 5)
		fmt.Printf("%-35s → %s (variance: %.4f)\n", series.name, phase, variance)
	}
	fmt.Println()

	// Show full explanation
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println("DETAILED MATHEMATICAL EXPLANATION:")
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println(theorem.ExplainOptimality())

	// Export to Lean 4
	fmt.Println()
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	fmt.Println("LEAN 4 FORMAL PROOF (first 50 lines):")
	fmt.Println("═════════════════════════════════════════════════════════════════════")
	leanCode := theorem.ToLeanDefinition()
	lines := splitLines(leanCode)
	for i := 0; i < min(50, len(lines)); i++ {
		fmt.Println(lines[i])
	}
	if len(lines) > 50 {
		fmt.Printf("... (%d more lines)\n", len(lines)-50)
	}
	fmt.Println()

	fmt.Println("Full Lean proof available at:")
	fmt.Println("  AsymmetricaProofs/ThreeRegimeDerivation.lean")
	fmt.Println()
	fmt.Println("Documentation available at:")
	fmt.Println("  docs/THREE_REGIME_DERIVATION.md")
	fmt.Println()
	fmt.Println("Om Lokah Samastah Sukhino Bhavantu 🙏")
}

func splitLines(s string) []string {
	result := []string{}
	current := ""
	for i := 0; i < len(s); i++ {
		if s[i] == '\n' {
			result = append(result, current)
			current = ""
		} else {
			current += string(s[i])
		}
	}
	if len(current) > 0 {
		result = append(result, current)
	}
	return result
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
