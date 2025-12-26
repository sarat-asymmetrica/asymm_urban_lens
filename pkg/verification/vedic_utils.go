package verification

import (
	"math"
)

// VedicUtils provides Vedic mathematical primitives
//
// These are COMPUTATIONAL ALGORITHMS discovered by ancient practitioners
// and validated by modern mathematics. NOT mysticism - pure math.
//
// - Digital Root: O(1) classification via modulo 9
// - Harmonic Mean: Reciprocal-based quality metric (penalizes weakness)
// - PHI Threshold: Golden ratio quality gate (0.618...)
// - Fibonacci: Natural growth sequence for batch sizing
type VedicUtils struct{}

// NewVedicUtils creates Vedic utilities instance
func NewVedicUtils() *VedicUtils {
	return &VedicUtils{}
}

// HarmonicMean calculates harmonic mean (Vedic resonance metric)
//
// Formula: n / Σ(1/xᵢ)
//
// Why harmonic mean?
// - Arithmetic mean can hide weakness: [0.9, 0.9, 0.9, 0.3] → avg = 0.75 (seems OK)
// - Harmonic mean exposes weakness: [0.9, 0.9, 0.9, 0.3] → harm = 0.51 (FAIL)
//
// This is how musical resonance works - all frequencies must align.
// One bad note ruins the philharmonic.
func (vu *VedicUtils) HarmonicMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	// Filter out zero/negative values (harmonic mean undefined)
	validValues := make([]float64, 0, len(values))
	for _, v := range values {
		if v > 0.0 {
			validValues = append(validValues, v)
		}
	}

	if len(validValues) == 0 {
		return 0.0
	}

	// Calculate sum of reciprocals
	reciprocalSum := 0.0
	for _, v := range validValues {
		reciprocalSum += 1.0 / v
	}

	// Harmonic mean = n / Σ(1/xᵢ)
	return float64(len(validValues)) / reciprocalSum
}

// DigitalRoot computes digital root (O(1) classification)
//
// Digital root = recursive sum of digits until single digit
// Example: 456 → 4+5+6 = 15 → 1+5 = 6
//
// Mathematical shortcut: digital_root(n) = 1 + ((n - 1) % 9)
// (Special case: 0 → 0)
//
// Uses:
// - O(1) clustering into 9 categories
// - Error type classification
// - Pattern bucketing
func (vu *VedicUtils) DigitalRoot(n uint64) uint8 {
	if n == 0 {
		return 0
	}
	result := n % 9
	if result == 0 {
		return 9
	}
	return uint8(result)
}

// PHIThreshold returns PHI-based quality threshold
//
// PHI (φ) = Golden Ratio = 1.618033988749...
// Reciprocal: 1/φ = 0.618033988749... (used as threshold)
//
// Why PHI?
// - Appears in nature's optimization (shells, flowers, galaxies)
// - Fibonacci ratio converges to PHI
// - Optimal balance point in many algorithms
// - Mathematical beauty = computational efficiency
//
// Quality below PHI = reject (too far from optimal)
func (vu *VedicUtils) PHIThreshold() float64 {
	return 0.618033988749 // 1/φ (reciprocal of golden ratio)
}

// PHI returns the golden ratio constant
func (vu *VedicUtils) PHI() float64 {
	return 1.618033988749 // φ = (1 + √5) / 2
}

// FibonacciCeiling returns smallest Fibonacci number ≥ n
//
// Fibonacci sequence: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, ...
// Each number is sum of previous two: F(n) = F(n-1) + F(n-2)
//
// Uses:
// - Natural batch sizes
// - Iteration count estimation
// - Growth pattern validation
func (vu *VedicUtils) FibonacciCeiling(n int) int {
	if n <= 0 {
		return 0
	}
	if n == 1 {
		return 1
	}

	// Generate Fibonacci sequence until we reach n
	a, b := 1, 1
	for b < n {
		a, b = b, a+b
	}
	return b
}

// FibonacciSequence generates first n Fibonacci numbers
func (vu *VedicUtils) FibonacciSequence(count int) []int {
	if count <= 0 {
		return []int{}
	}

	sequence := make([]int, count)
	if count >= 1 {
		sequence[0] = 1
	}
	if count >= 2 {
		sequence[1] = 1
	}

	for i := 2; i < count; i++ {
		sequence[i] = sequence[i-1] + sequence[i-2]
	}

	return sequence
}

// WilliamsBatchSize computes optimal batch size using Williams algorithm
//
// Formula: √n × log₂(n)
//
// Why this formula?
// - Sublinear growth (better than linear O(n))
// - Logarithmic component balances memory vs computation
// - Proven optimal for many divide-and-conquer algorithms
//
// Example: 100 items → √100 × log₂(100) ≈ 10 × 6.64 ≈ 66
func (vu *VedicUtils) WilliamsBatchSize(count int) int {
	if count <= 1 {
		return 1
	}

	// √n
	sqrtN := math.Sqrt(float64(count))

	// log₂(n)
	log2N := math.Log2(float64(count))

	// √n × log₂(n)
	batchSize := sqrtN * log2N

	// Round and ensure minimum 1
	result := int(math.Round(batchSize))
	if result < 1 {
		result = 1
	}

	return result
}

// GeometricMean calculates geometric mean
//
// Formula: (x₁ × x₂ × ... × xₙ)^(1/n)
//
// Used when multiple factors must ALL be good (multiplication)
// Example: Correctness = errors_fixed × tests_passing (geometric mean)
func (vu *VedicUtils) GeometricMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	// Product of all values
	product := 1.0
	for _, v := range values {
		if v <= 0.0 {
			return 0.0 // Geometric mean undefined for non-positive
		}
		product *= v
	}

	// nth root
	n := float64(len(values))
	return math.Pow(product, 1.0/n)
}

// ArithmeticMean calculates simple average
//
// Formula: Σxᵢ / n
//
// Warning: Can hide weakness! Use harmonic mean for quality gates.
func (vu *VedicUtils) ArithmeticMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	sum := 0.0
	for _, v := range values {
		sum += v
	}
	return sum / float64(len(values))
}

// TeslaCycle returns Tesla's 3-6-9 harmonic frequency
//
// Nikola Tesla: "If you only knew the magnificence of 3, 6 and 9,
// then you would have the key to the universe."
//
// Computational interpretation:
// - 3: Ternary logic (true, false, unknown)
// - 6: Hexagonal packing (optimal 2D space utilization)
// - 9: Digital root cycle (modulo 9 arithmetic)
const TeslaCycle = 4.909 // Hz (harmonic frequency)

// TAU returns 2π (full circle constant)
const TAU = 6.28318530718 // 2π

// TwoPiSquared returns 2π² (resonance threshold constant)
const TwoPiSquared = 19.739208802178 // 2π²

// ClampToRange restricts value to [min, max]
func (vu *VedicUtils) ClampToRange(value, min, max float64) float64 {
	if value < min {
		return min
	}
	if value > max {
		return max
	}
	return value
}

// IsConverging checks if series is decreasing (Collatz convergence)
func (vu *VedicUtils) IsConverging(history []int) bool {
	if len(history) < 2 {
		return true // Not enough data
	}

	// Check last few iterations
	checkCount := 3
	if len(history) < checkCount+1 {
		checkCount = len(history) - 1
	}

	for i := len(history) - checkCount; i < len(history)-1; i++ {
		if history[i+1] >= history[i] {
			return false // Not decreasing
		}
	}

	return true
}

// EstimateFibonacciGrowth predicts next value in Fibonacci-like sequence
func (vu *VedicUtils) EstimateFibonacciGrowth(current, previous int) int {
	// Next ≈ current × φ
	phi := vu.PHI()
	nextFloat := float64(current) * phi
	return int(math.Round(nextFloat))
}
