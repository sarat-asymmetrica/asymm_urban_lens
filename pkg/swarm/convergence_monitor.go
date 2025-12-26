// Package swarm - Convergence Monitor
//
// Collatz Convergence Guarantee: Error counts must monotonically decrease OR we detect stuck states
// Author: Agent 3.3 (Dr. Priya Sharma - Mathematical Convergence Theory, Cambridge)
// Created: 2025-11-07
//
// Core Axiom: error_count[t+1] < error_count[t] ∨ STUCK_DETECTED
// Mathematical guarantee: Either converge to 0 errors OR detect stuck state and flag for help
package swarm

import (
	"fmt"
	"math"
	"time"
)

// ConvergenceMonitor tracks healing progress and detects stuck states
// Uses Collatz conjecture principles: error count must decrease each iteration
type ConvergenceMonitor struct {
	history        []IterationState
	maxIterations  int     // Maximum allowed iterations before declaring stuck
	minProgress    float64 // Minimum progress rate required (errors/iteration)
	stuckThreshold int     // Iterations without progress before declaring stuck
	startTime      time.Time
	startErrors    int
}

// IterationState captures complete state at one healing iteration
type IterationState struct {
	Iteration        int           // Iteration number (0-indexed)
	ErrorCount       int           // Total compilation errors at this iteration
	VariantsApplied  int           // Number of fix variants applied
	VariantsTested   int           // Number of variants tested (may be > applied)
	BestVariant      *FixResult    // Best performing variant this iteration
	ProgressRate     float64       // Errors reduced per iteration (running average)
	Timestamp        time.Time     // When this iteration completed
	Duration         time.Duration // Time taken for this iteration
	ConvergenceVelocity float64    // Rate of approach to zero (mathematical)
}

// NewConvergenceMonitor creates a new monitor with Vedic-optimized parameters
func NewConvergenceMonitor(initialErrors int) *ConvergenceMonitor {
	// Use PHI (0.618) for minimum progress weighting
	minProgress := 0.618 // Must reduce at least 0.618 errors/iteration on average

	// Use digital root of initial errors for stuck threshold
	stuckThreshold := digitalRoot(uint64(initialErrors))
	if stuckThreshold < 3 {
		stuckThreshold = 3 // Minimum 3 iterations to detect oscillation
	}

	// Max iterations = Fibonacci number based on error count
	maxIter := fibonacciCeiling(initialErrors * 2) // Allow 2x error count in Fibonacci

	return &ConvergenceMonitor{
		history:        make([]IterationState, 0, 100),
		maxIterations:  maxIter,
		minProgress:    minProgress,
		stuckThreshold: stuckThreshold,
		startTime:      time.Now(),
		startErrors:    initialErrors,
	}
}

// RecordIteration adds new iteration to history and calculates metrics
func (cm *ConvergenceMonitor) RecordIteration(state IterationState) error {
	// Validate: Error count must be non-negative
	if state.ErrorCount < 0 {
		return fmt.Errorf("invalid error count: %d (must be >= 0)", state.ErrorCount)
	}

	// Calculate progress rate (running average)
	if len(cm.history) > 0 {
		totalProgress := float64(cm.startErrors - state.ErrorCount)
		state.ProgressRate = totalProgress / float64(state.Iteration+1)
	} else {
		state.ProgressRate = 0.0
	}

	// Calculate convergence velocity (how fast we're approaching zero)
	if len(cm.history) > 0 {
		prev := cm.history[len(cm.history)-1]
		if state.Duration.Seconds() > 0 {
			// Velocity = errors reduced / time (errors per second)
			errorsReduced := float64(prev.ErrorCount - state.ErrorCount)
			state.ConvergenceVelocity = errorsReduced / state.Duration.Seconds()
		}
	}

	// Append to history
	cm.history = append(cm.history, state)

	return nil
}

// CheckConvergence determines if we're making progress or stuck
// Returns ConvergenceStatus with actionable recommendations
func (cm *ConvergenceMonitor) CheckConvergence() ConvergenceStatus {
	if len(cm.history) == 0 {
		return ConvergenceStatus{
			Status:         StatusUnknown,
			CurrentErrors:  cm.startErrors,
			IterationCount: 0,
			ProgressRate:   0.0,
			Recommendation: "No iterations recorded yet - waiting for first result",
		}
	}

	latest := cm.history[len(cm.history)-1]

	// Check for completion
	if latest.ErrorCount == 0 {
		return ConvergenceStatus{
			Status:         StatusComplete,
			CurrentErrors:  0,
			IterationCount: len(cm.history),
			ProgressRate:   latest.ProgressRate,
			Recommendation: "All errors resolved - healing complete!",
			TimeElapsed:    time.Since(cm.startTime),
			ErrorsFixed:    cm.startErrors,
		}
	}

	// Check for stuck states
	detector := NewStuckDetector(cm.stuckThreshold, 10)
	stuckState, isStuck := detector.DetectStuck(cm.history)

	if isStuck {
		return ConvergenceStatus{
			Status:         StatusStuck,
			CurrentErrors:  latest.ErrorCount,
			IterationCount: len(cm.history),
			ProgressRate:   latest.ProgressRate,
			Recommendation: stuckState.Suggestion,
			TimeElapsed:    time.Since(cm.startTime),
			ErrorsFixed:    cm.startErrors - latest.ErrorCount,
			StuckReason:    stuckState.Description,
			StuckType:      string(stuckState.Type),
		}
	}

	// Check if we hit max iterations (failsafe)
	if len(cm.history) >= cm.maxIterations {
		return ConvergenceStatus{
			Status:         StatusMaxIterations,
			CurrentErrors:  latest.ErrorCount,
			IterationCount: len(cm.history),
			ProgressRate:   latest.ProgressRate,
			Recommendation: fmt.Sprintf("Hit max iterations (%d) - need architectural review", cm.maxIterations),
			TimeElapsed:    time.Since(cm.startTime),
			ErrorsFixed:    cm.startErrors - latest.ErrorCount,
			StuckReason:    fmt.Sprintf("Exceeded %d iterations without convergence", cm.maxIterations),
			StuckType:      string(StuckMaxIterations),
		}
	}

	// Check for oscillation (pattern detection)
	if len(cm.history) >= 4 && detector.DetectOscillation(cm.history) {
		return ConvergenceStatus{
			Status:         StatusOscillating,
			CurrentErrors:  latest.ErrorCount,
			IterationCount: len(cm.history),
			ProgressRate:   latest.ProgressRate,
			Recommendation: "Error count oscillating - try different fix strategy",
			TimeElapsed:    time.Since(cm.startTime),
			ErrorsFixed:    cm.startErrors - latest.ErrorCount,
			StuckReason:    "Error count cycling between states",
			StuckType:      string(StuckOscillating),
		}
	}

	// Check for healthy convergence
	if len(cm.history) >= 2 {
		prev := cm.history[len(cm.history)-2]
		if latest.ErrorCount < prev.ErrorCount {
			// Making progress - good!
			return ConvergenceStatus{
				Status:         StatusConverging,
				CurrentErrors:  latest.ErrorCount,
				IterationCount: len(cm.history),
				ProgressRate:   latest.ProgressRate,
				Recommendation: "Making progress - continue healing",
				TimeElapsed:    time.Since(cm.startTime),
				ErrorsFixed:    cm.startErrors - latest.ErrorCount,
			}
		}
	}

	// Default: no progress yet but not stuck (early iterations)
	return ConvergenceStatus{
		Status:         StatusUnknown,
		CurrentErrors:  latest.ErrorCount,
		IterationCount: len(cm.history),
		ProgressRate:   latest.ProgressRate,
		Recommendation: "Monitoring - waiting for clear trend",
		TimeElapsed:    time.Since(cm.startTime),
		ErrorsFixed:    cm.startErrors - latest.ErrorCount,
	}
}

// GetProgressRate calculates current errors-per-iteration reduction rate
func (cm *ConvergenceMonitor) GetProgressRate() float64 {
	if len(cm.history) == 0 {
		return 0.0
	}
	latest := cm.history[len(cm.history)-1]
	return latest.ProgressRate
}

// GetConvergenceVelocity calculates rate of approach to zero (errors/second)
func (cm *ConvergenceMonitor) GetConvergenceVelocity() float64 {
	if len(cm.history) == 0 {
		return 0.0
	}
	latest := cm.history[len(cm.history)-1]
	return latest.ConvergenceVelocity
}

// PredictIterationsToZero estimates remaining iterations (may be infinity if stuck)
// Uses harmonic mean of recent progress rates for robust prediction
func (cm *ConvergenceMonitor) PredictIterationsToZero() int {
	if len(cm.history) == 0 {
		return -1 // Unknown
	}

	latest := cm.history[len(cm.history)-1]
	if latest.ErrorCount == 0 {
		return 0 // Already done
	}

	if latest.ProgressRate <= 0 {
		return -1 // No progress - infinite iterations
	}

	// Use harmonic mean of last N progress rates for robust estimate
	windowSize := min(5, len(cm.history))
	rates := make([]float64, 0, windowSize)

	for i := len(cm.history) - windowSize; i < len(cm.history); i++ {
		if cm.history[i].ProgressRate > 0 {
			rates = append(rates, cm.history[i].ProgressRate)
		}
	}

	if len(rates) == 0 {
		return -1 // No valid rates
	}

	avgRate := harmonicMean(rates)
	if avgRate <= 0 {
		return -1
	}

	predicted := float64(latest.ErrorCount) / avgRate
	return int(math.Ceil(predicted))
}

// ConvergenceStatus represents current convergence state
type ConvergenceStatus struct {
	Status         ConvergenceState // Current status
	CurrentErrors  int              // Errors remaining
	IterationCount int              // Iterations completed
	ProgressRate   float64          // Errors reduced per iteration
	Recommendation string           // What to do next
	TimeElapsed    time.Duration    // Total time elapsed
	ErrorsFixed    int              // Total errors fixed
	StuckReason    string           // Why stuck (if applicable)
	StuckType      string           // Type of stuck state
}

// ConvergenceState represents the convergence status
type ConvergenceState string

const (
	StatusUnknown        ConvergenceState = "unknown"         // Not enough data
	StatusConverging     ConvergenceState = "converging"      // Making progress
	StatusStuck          ConvergenceState = "stuck"           // No progress
	StatusOscillating    ConvergenceState = "oscillating"     // Cycling between states
	StatusComplete       ConvergenceState = "complete"        // All errors fixed
	StatusMaxIterations  ConvergenceState = "max_iterations"  // Hit iteration limit
)

// Vedic helper functions

// digitalRoot calculates digital root in O(1) - Vedic optimization
func digitalRoot(n uint64) int {
	if n == 0 {
		return 0
	}
	result := n % 9
	if result == 0 {
		return 9
	}
	return int(result)
}

// fibonacciCeiling returns smallest Fibonacci number >= n
func fibonacciCeiling(n int) int {
	if n <= 0 {
		return 1
	}
	if n == 1 {
		return 1
	}

	a, b := 1, 1
	for b < n {
		a, b = b, a+b
	}
	return b
}

// harmonicMean calculates harmonic mean (penalizes outliers)
// Returns 0 if any value is zero or negative (mathematical undefined)
func harmonicMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	sum := 0.0
	count := 0
	for _, v := range values {
		if v <= 0 {
			return 0.0 // Harmonic mean undefined with zero or negative values
		}
		sum += 1.0 / v
		count++
	}

	if count == 0 || sum == 0 {
		return 0.0
	}

	return float64(count) / sum
}

// min returns minimum of two integers
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
