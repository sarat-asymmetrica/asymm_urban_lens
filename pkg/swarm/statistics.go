// Package swarm - Convergence Statistics
//
// Mathematical analysis of convergence metrics
// Author: Agent 3.3 (Dr. Priya Sharma - Mathematical Convergence Theory, Cambridge)
// Created: 2025-11-07
//
// Uses Vedic mathematics and statistical analysis for convergence predictions
package swarm

import (
	"math"
)

// Statistics calculates convergence metrics
type Statistics struct{}

// NewStatistics creates statistics calculator
func NewStatistics() *Statistics {
	return &Statistics{}
}

// CalculateProgressRate computes errors fixed per iteration
// Uses weighted moving average with PHI (golden ratio) weighting
func (s *Statistics) CalculateProgressRate(history []IterationState) float64 {
	if len(history) == 0 {
		return 0.0
	}

	// Simple rate: total progress / iterations
	latest := history[len(history)-1]
	if latest.Iteration == 0 {
		return 0.0
	}

	// Calculate from first to last (total progress)
	first := history[0]
	totalProgress := float64(first.ErrorCount - latest.ErrorCount)
	iterations := float64(latest.Iteration + 1)

	return totalProgress / iterations
}

// CalculateWeightedProgressRate uses PHI-weighted recent history
// Recent iterations matter more (exponential decay with PHI)
func (s *Statistics) CalculateWeightedProgressRate(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	// Use PHI (0.618) as decay factor - recent iterations weighted higher
	const phi = 0.618033988749

	weightedSum := 0.0
	totalWeight := 0.0

	for i := 1; i < len(history); i++ {
		prev := history[i-1]
		curr := history[i]

		progress := float64(prev.ErrorCount - curr.ErrorCount)

		// Weight decreases exponentially for older iterations
		// Most recent = weight 1.0, previous = phi, previous = phi^2, etc.
		age := float64(len(history) - i - 1)
		weight := math.Pow(phi, age)

		weightedSum += progress * weight
		totalWeight += weight
	}

	if totalWeight == 0 {
		return 0.0
	}

	return weightedSum / totalWeight
}

// CalculateConvergenceVelocity measures how fast we're approaching zero
// Returns errors per second (instantaneous velocity)
func (s *Statistics) CalculateConvergenceVelocity(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	// Use last two iterations for instantaneous velocity
	prev := history[len(history)-2]
	curr := history[len(history)-1]

	errorsReduced := float64(prev.ErrorCount - curr.ErrorCount)
	timeTaken := curr.Duration.Seconds()

	if timeTaken <= 0 {
		return 0.0
	}

	return errorsReduced / timeTaken
}

// CalculateAverageVelocity computes average velocity across all iterations
func (s *Statistics) CalculateAverageVelocity(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	first := history[0]
	latest := history[len(history)-1]

	totalErrors := float64(first.ErrorCount - latest.ErrorCount)
	totalTime := latest.Timestamp.Sub(first.Timestamp).Seconds()

	if totalTime <= 0 {
		return 0.0
	}

	return totalErrors / totalTime
}

// PredictIterationsToZero estimates remaining iterations
// Uses harmonic mean of recent progress rates for robust prediction
func (s *Statistics) PredictIterationsToZero(history []IterationState) int {
	if len(history) == 0 {
		return -1 // Unknown
	}

	latest := history[len(history)-1]
	if latest.ErrorCount == 0 {
		return 0 // Already done
	}

	// Collect recent progress rates
	windowSize := min(5, len(history))
	rates := make([]float64, 0, windowSize)

	for i := 1; i < len(history) && len(rates) < windowSize; i++ {
		prev := history[len(history)-i-1]
		curr := history[len(history)-i]
		progress := float64(prev.ErrorCount - curr.ErrorCount)
		if progress > 0 {
			rates = append(rates, progress)
		}
	}

	if len(rates) == 0 {
		return -1 // No progress data
	}

	// Use harmonic mean (more robust to outliers than arithmetic mean)
	avgRate := harmonicMean(rates)
	if avgRate <= 0 {
		return -1
	}

	predicted := float64(latest.ErrorCount) / avgRate
	return int(math.Ceil(predicted))
}

// CalculateConfidenceInterval gives [min, max] iterations with 95% confidence
// Uses standard deviation of recent progress rates
func (s *Statistics) CalculateConfidenceInterval(history []IterationState) (int, int) {
	if len(history) < 3 {
		return -1, -1 // Insufficient data
	}

	latest := history[len(history)-1]
	if latest.ErrorCount == 0 {
		return 0, 0 // Already done
	}

	// Collect recent progress rates
	rates := make([]float64, 0, len(history))
	for i := 1; i < len(history); i++ {
		prev := history[i-1]
		curr := history[i]
		progress := float64(prev.ErrorCount - curr.ErrorCount)
		if progress >= 0 {
			rates = append(rates, progress)
		}
	}

	if len(rates) < 2 {
		return -1, -1
	}

	// Calculate mean and standard deviation
	mean := arithmeticMean(rates)
	stdDev := standardDeviation(rates, mean)

	if mean <= 0 {
		return -1, -1
	}

	// 95% confidence interval: mean ± 1.96 * stdDev
	// For iterations: errors / (mean ± 1.96*stdDev)
	minRate := mean + 1.96*stdDev // Higher rate = fewer iterations
	maxRate := mean - 1.96*stdDev // Lower rate = more iterations

	if minRate <= 0 {
		minRate = mean / 2.0 // Fallback
	}
	if maxRate <= 0 {
		return -1, -1 // Cannot converge
	}

	minIter := int(math.Ceil(float64(latest.ErrorCount) / minRate))
	maxIter := int(math.Ceil(float64(latest.ErrorCount) / maxRate))

	return minIter, maxIter
}

// CalculateHarmonicQuality computes harmonic mean of convergence quality
// Quality = [progress_rate, velocity, consistency, trend]
// Uses Vedic harmonic mean (penalizes weak dimensions)
func (s *Statistics) CalculateHarmonicQuality(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	// Dimension 1: Progress rate (normalized 0-1)
	progressRate := s.CalculateProgressRate(history)
	normalizedRate := normalizeRate(progressRate, history[0].ErrorCount)

	// Dimension 2: Velocity (normalized 0-1)
	velocity := s.CalculateConvergenceVelocity(history)
	normalizedVelocity := normalizeVelocity(velocity, history)

	// Dimension 3: Consistency (how stable is progress?)
	consistency := s.calculateConsistency(history)

	// Dimension 4: Trend (are we accelerating?)
	trend := s.calculateTrend(history)

	// Harmonic mean of four quality dimensions
	dimensions := []float64{normalizedRate, normalizedVelocity, consistency, trend}
	return harmonicMean(dimensions)
}

// calculateConsistency measures how consistent progress is (0-1)
// High consistency = steady progress, Low = erratic
func (s *Statistics) calculateConsistency(history []IterationState) float64 {
	if len(history) < 3 {
		return 0.5 // Neutral
	}

	// Calculate coefficient of variation for progress rates
	rates := make([]float64, 0, len(history)-1)
	for i := 1; i < len(history); i++ {
		prev := history[i-1]
		curr := history[i]
		progress := float64(prev.ErrorCount - curr.ErrorCount)
		rates = append(rates, progress)
	}

	if len(rates) < 2 {
		return 0.5
	}

	mean := arithmeticMean(rates)
	if mean <= 0 {
		return 0.0
	}

	stdDev := standardDeviation(rates, mean)
	cv := stdDev / mean // Coefficient of variation

	// Convert to 0-1 scale: low CV = high consistency
	// CV > 1.0 means very inconsistent
	consistency := 1.0 / (1.0 + cv)
	return consistency
}

// calculateTrend measures if we're accelerating (positive) or slowing (negative)
// Returns 0-1 where >0.5 = accelerating, <0.5 = decelerating
func (s *Statistics) calculateTrend(history []IterationState) float64 {
	if len(history) < 3 {
		return 0.5 // Neutral
	}

	// Compare first half vs second half velocities
	mid := len(history) / 2
	firstHalf := history[:mid]
	secondHalf := history[mid:]

	firstVelocity := s.CalculateAverageVelocity(firstHalf)
	secondVelocity := s.CalculateAverageVelocity(secondHalf)

	if firstVelocity <= 0 {
		return 0.5
	}

	// Ratio > 1 = accelerating, < 1 = decelerating
	ratio := secondVelocity / firstVelocity

	// Normalize to 0-1 scale (sigmoid)
	// ratio = 2.0 → trend = 0.88 (accelerating)
	// ratio = 1.0 → trend = 0.5 (stable)
	// ratio = 0.5 → trend = 0.12 (decelerating)
	trend := 1.0 / (1.0 + math.Exp(-2.0*(ratio-1.0)))
	return trend
}

// Helper functions

// arithmeticMean calculates simple average
func arithmeticMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}
	sum := 0.0
	for _, v := range values {
		sum += v
	}
	return sum / float64(len(values))
}

// standardDeviation calculates sample standard deviation
func standardDeviation(values []float64, mean float64) float64 {
	if len(values) < 2 {
		return 0.0
	}

	variance := 0.0
	for _, v := range values {
		diff := v - mean
		variance += diff * diff
	}
	variance /= float64(len(values) - 1) // Sample variance

	return math.Sqrt(variance)
}

// normalizeRate converts progress rate to 0-1 scale
func normalizeRate(rate float64, totalErrors int) float64 {
	if totalErrors == 0 {
		return 1.0
	}

	// Ideal rate = fix all errors in 1 iteration
	ideal := float64(totalErrors)

	// Normalize: rate / ideal
	normalized := rate / ideal
	if normalized > 1.0 {
		normalized = 1.0
	}
	if normalized < 0.0 {
		normalized = 0.0
	}

	return normalized
}

// normalizeVelocity converts velocity to 0-1 scale
func normalizeVelocity(velocity float64, history []IterationState) float64 {
	if len(history) == 0 || velocity <= 0 {
		return 0.0
	}

	// Ideal velocity = fix all errors in 1 second
	ideal := float64(history[0].ErrorCount)

	// Normalize: velocity / ideal
	normalized := velocity / ideal
	if normalized > 1.0 {
		normalized = 1.0
	}

	return normalized
}

// CalculateCollatzNumber returns Collatz sequence length for error count
// Used as diagnostic: long sequences suggest complex convergence
func (s *Statistics) CalculateCollatzNumber(errorCount int) int {
	if errorCount <= 0 {
		return 0
	}

	n := errorCount
	steps := 0

	for n > 1 && steps < 1000 { // Safety limit
		if n%2 == 0 {
			n = n / 2
		} else {
			n = 3*n + 1
		}
		steps++
	}

	return steps
}

// PredictConvergenceComplexity estimates convergence difficulty (0-1)
// Based on: initial error count, Collatz number, digital root
// Higher = more difficult convergence expected
func (s *Statistics) PredictConvergenceComplexity(initialErrors int) float64 {
	// Factor 1: Error count (normalized by log)
	errorFactor := math.Log10(float64(initialErrors+1)) / math.Log10(100.0)
	if errorFactor > 1.0 {
		errorFactor = 1.0
	}

	// Factor 2: Collatz number (normalized)
	collatz := s.CalculateCollatzNumber(initialErrors)
	collatzFactor := float64(collatz) / 100.0
	if collatzFactor > 1.0 {
		collatzFactor = 1.0
	}

	// Factor 3: Digital root (certain numbers harder to work with)
	dr := digitalRoot(uint64(initialErrors))
	// Digital roots 3, 6, 9 are harder (divisible by 3 = more complex factors)
	drFactor := 0.5
	if dr%3 == 0 {
		drFactor = 0.8
	}

	// Combine using harmonic mean (penalizes easy factors)
	factors := []float64{errorFactor, collatzFactor, drFactor}
	complexity := harmonicMean(factors)

	return complexity
}
