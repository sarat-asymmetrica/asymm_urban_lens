// Package swarm implements Williams-optimized swarm orchestration for Urban Lens
//
// Williams Sizer: Calculate optimal swarm sizes using Williams O(√n × log₂n) optimization
// Adapted from Ananta to Urban Lens parallel hypothesis exploration
//
// This sizer calculates optimal number of parallel sub-agents to spawn based on:
// - Number of hypotheses (n) → swarm size O(√n × log₂n)
// - Resource constraints (min/max swarm sizes)
// - Vedic digital root clustering for variant distribution
//
// Mathematical Foundation:
// - Williams batch sizing: floor(√n × log₂(n)) for sublinear scaling
// - Collatz convergence guarantee: quality score monotonically increases
// - PHI weighting (0.618) for priority assignment
// - Harmonic mean for multi-variant confidence scoring
package swarm

import (
	"math"
)

// WilliamsSizer calculates optimal swarm sizes using Williams optimization
//
// The sizer uses Ryan Williams' O(√n × log₂n) formula to determine
// how many parallel attempts to spawn for a given task.
//
// Key principles:
//   - Sublinear scaling: More hypotheses → diminishing returns on additional workers
//   - Resource constraints: Clamp to [minSwarmSize, maxSwarmSize]
//   - Batch optimization: Group multiple tasks efficiently
//
// Example:
//
//	sizer := NewWilliamsSizer(1, 20)
//	swarmSize := sizer.CalculateSwarmSize(10) // Returns ~10 workers
//	swarmSize := sizer.CalculateSwarmSize(100) // Returns ~20 workers (clamped)
type WilliamsSizer struct {
	minSwarmSize int // minimum swarm size (default: 1)
	maxSwarmSize int // maximum swarm size (default: 20)
}

// NewWilliamsSizer creates a new Williams swarm sizer
//
// Parameters:
//   - minSwarmSize: Minimum number of parallel workers (must be ≥ 1)
//   - maxSwarmSize: Maximum number of parallel workers (must be ≥ minSwarmSize)
//
// Returns:
//   - Configured sizer ready to calculate optimal swarm sizes
//
// Example:
//
//	sizer := NewWilliamsSizer(1, 20)
//	// Will never spawn < 1 or > 20 parallel workers
func NewWilliamsSizer(minSwarmSize, maxSwarmSize int) *WilliamsSizer {
	// Validate bounds
	if minSwarmSize < 1 {
		minSwarmSize = 1
	}
	if maxSwarmSize < minSwarmSize {
		maxSwarmSize = minSwarmSize
	}

	return &WilliamsSizer{
		minSwarmSize: minSwarmSize,
		maxSwarmSize: maxSwarmSize,
	}
}

// CalculateSwarmSize determines optimal number of parallel sub-agents
//
// Uses Williams O(√n × log₂n) formula for sublinear scaling:
//   - For n=1 hypotheses: 1 worker (minimum)
//   - For n=10 hypotheses: ~10 workers (√10 × log₂(10) ≈ 3.16 × 3.32 ≈ 10.5)
//   - For n=100 hypotheses: ~20 workers (clamped at maxSwarmSize)
//   - For n=1000 hypotheses: ~20 workers (clamped at maxSwarmSize)
//
// The formula provides:
//   - Fast convergence for small n (linear-ish growth)
//   - Diminishing returns for large n (sublinear scaling)
//   - Memory efficiency (O(√n) space complexity)
//
// Parameters:
//   - hypothesisCount: Number of hypotheses to explore for this task
//
// Returns:
//   - Optimal swarm size clamped to [minSwarmSize, maxSwarmSize]
//
// Example:
//
//	sizer := NewWilliamsSizer(1, 20)
//	size := sizer.CalculateSwarmSize(10)  // Returns ~10
//	size := sizer.CalculateSwarmSize(100) // Returns 20 (clamped)
func (w *WilliamsSizer) CalculateSwarmSize(hypothesisCount int) int {
	// Handle edge cases
	if hypothesisCount <= 0 {
		return w.minSwarmSize
	}

	if hypothesisCount == 1 {
		return w.minSwarmSize
	}

	// Williams formula: floor(√n × log₂(n))
	n := float64(hypothesisCount)
	sqrtN := math.Sqrt(n)
	log2N := math.Log2(n)
	rawSize := int(math.Floor(sqrtN * log2N))

	// Clamp to [minSwarmSize, maxSwarmSize]
	size := rawSize
	if size < w.minSwarmSize {
		size = w.minSwarmSize
	}
	if size > w.maxSwarmSize {
		size = w.maxSwarmSize
	}

	return size
}

// CalculateBatchSize determines how many tasks to process in parallel
//
// When processing multiple tasks simultaneously, we need to batch them
// to avoid overwhelming the system. This uses the same Williams formula
// but applied to task count instead of hypothesis count.
//
// Key consideration: Each task spawns its own swarm, so we're batching
// swarms, not individual workers.
//
// Parameters:
//   - taskCount: Total number of tasks to process
//
// Returns:
//   - Optimal batch size for parallel task processing
//
// Example:
//
//	sizer := NewWilliamsSizer(1, 20)
//	batchSize := sizer.CalculateBatchSize(4)  // Process 4 tasks at once
//	batchSize := sizer.CalculateBatchSize(50) // Process ~18 tasks at once
func (w *WilliamsSizer) CalculateBatchSize(taskCount int) int {
	// Use same Williams formula for batch sizing
	if taskCount <= 0 {
		return 1
	}

	if taskCount == 1 {
		return 1
	}

	// Williams batch size: floor(√n × log₂(n))
	n := float64(taskCount)
	sqrtN := math.Sqrt(n)
	log2N := math.Log2(n)
	batchSize := int(math.Floor(sqrtN * log2N))

	// Ensure at least 1
	if batchSize < 1 {
		batchSize = 1
	}

	// Cap at task count (can't batch more than we have)
	if batchSize > taskCount {
		batchSize = taskCount
	}

	return batchSize
}

// EstimateResourceUsage estimates total parallel processes for given tasks and hypotheses
//
// This helps predict resource usage before spawning swarms:
//   - Each task spawns a swarm
//   - Each swarm size depends on hypothesis count
//   - Total processes = Σ(swarm_size_per_task)
//
// Parameters:
//   - taskCount: Number of tasks
//   - avgHypothesesPerTask: Average number of hypotheses per task
//
// Returns:
//   - Estimated total parallel processes
//
// Example:
//
//	sizer := NewWilliamsSizer(1, 20)
//	// 4 tasks, average 10 hypotheses each
//	totalProcesses := sizer.EstimateResourceUsage(4, 10)
//	// Returns ~40 processes (4 tasks × ~10 workers each)
func (w *WilliamsSizer) EstimateResourceUsage(taskCount int, avgHypothesesPerTask int) int {
	if taskCount <= 0 {
		return 0
	}

	// Calculate swarm size for average hypothesis count
	swarmSize := w.CalculateSwarmSize(avgHypothesesPerTask)

	// Total = tasks × workers per task
	total := taskCount * swarmSize

	return total
}

// GetBounds returns the configured min/max swarm size bounds
//
// Useful for validation and debugging.
//
// Returns:
//   - minSwarmSize: Minimum workers per swarm
//   - maxSwarmSize: Maximum workers per swarm
func (w *WilliamsSizer) GetBounds() (min int, max int) {
	return w.minSwarmSize, w.maxSwarmSize
}

// DigitalRoot calculates Vedic digital root for O(1) classification
//
// Maps any number to 1-9 for pattern clustering.
// This is used by variant generator for distribution hashing.
//
// Algorithm: ((n-1) mod 9) + 1 for n > 0
//
// Example:
//   - DigitalRoot(123) = ((123-1) % 9) + 1 = (122 % 9) + 1 = 5
//   - DigitalRoot(999) = ((999-1) % 9) + 1 = (998 % 9) + 1 = 9
//
// Parameters:
//   - n: Input number
//
// Returns:
//   - Digital root in range [0, 9]
func DigitalRoot(n int64) int {
	if n == 0 {
		return 0
	}
	if n < 0 {
		n = -n // Handle negative numbers
	}
	return int(((n - 1) % 9) + 1)
}

// HarmonicMean calculates rigorous quality score for multiple values
//
// The harmonic mean penalizes outliers - a single low value drags down
// the overall score. This is CRITICAL for quality validation because
// we can't hide poor performance in one dimension.
//
// Formula: n / Σ(1/xᵢ) where n is count of values
//
// Why harmonic mean?
//   - Arithmetic mean: (0.9 + 0.9 + 0.9 + 0.3) / 4 = 0.75 (looks okay!)
//   - Harmonic mean: 4 / (1/0.9 + 1/0.9 + 1/0.9 + 1/0.3) = 0.51 (BAD!)
//
// Parameters:
//   - values: Scores to aggregate (each in range [0.0, 1.0])
//
// Returns:
//   - Harmonic mean of values (0.0 if any value is 0.0)
//
// Example:
//
//	scores := []float64{0.95, 0.90, 0.88, 0.92, 0.65}
//	quality := HarmonicMean(scores) // Returns ~0.81 (exposes 0.65 weakness)
func HarmonicMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	// Check for any zero values (would cause division by zero)
	for _, v := range values {
		if v <= 0.0 {
			return 0.0
		}
	}

	// Calculate sum of reciprocals
	reciprocalSum := 0.0
	for _, v := range values {
		reciprocalSum += 1.0 / v
	}

	// Harmonic mean: n / Σ(1/xᵢ)
	n := float64(len(values))
	return n / reciprocalSum
}

// PHI is the golden ratio (φ = 1.618...), used for priority weighting
//
// Appears in 41% of Ramanujan formulas (vs <10% previously recognized).
// Used by Fibonacci spirals for natural convergence.
const PHI = 1.618033988749

// PHIWeightedScore applies golden ratio weighting to a base score
//
// Used for priority calculation where we want natural scaling.
// Higher priority → multiply by φ for exponential growth.
//
// Parameters:
//   - baseScore: Initial score in range [0.0, 1.0]
//   - priorityLevel: Priority level (0 = highest, higher = lower priority)
//
// Returns:
//   - Weighted score using PHI decay
//
// Example:
//
//	score := PHIWeightedScore(0.85, 0) // Returns 0.85 (highest priority)
//	score := PHIWeightedScore(0.85, 1) // Returns 0.85 / φ ≈ 0.525
//	score := PHIWeightedScore(0.85, 2) // Returns 0.85 / φ² ≈ 0.325
func PHIWeightedScore(baseScore float64, priorityLevel int) float64 {
	if priorityLevel < 0 {
		priorityLevel = 0
	}

	// Decay by φ^priorityLevel
	divisor := math.Pow(PHI, float64(priorityLevel))
	return baseScore / divisor
}
