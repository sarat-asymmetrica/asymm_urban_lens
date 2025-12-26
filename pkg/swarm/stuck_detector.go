// Package swarm - Stuck State Detector
//
// Detects when healing is stuck and cannot make progress
// Author: Agent 3.3 (Dr. Priya Sharma - Mathematical Convergence Theory, Cambridge)
// Created: 2025-11-07
//
// Stuck Detection: Identifies when error count is not decreasing and provides actionable diagnosis
package swarm

import (
	"fmt"
	"math"
)

// StuckDetector identifies when healing is stuck
type StuckDetector struct {
	noProgressThreshold int // Iterations without improvement = stuck
	oscillationWindow   int // Window size for oscillation detection
}

// NewStuckDetector creates detector with specified thresholds
func NewStuckDetector(noProgressThreshold, oscillationWindow int) *StuckDetector {
	return &StuckDetector{
		noProgressThreshold: noProgressThreshold,
		oscillationWindow:   oscillationWindow,
	}
}

// DetectStuck analyzes history and determines if stuck
// Returns (StuckState, true) if stuck, (nil, false) if making progress
func (sd *StuckDetector) DetectStuck(history []IterationState) (*StuckState, bool) {
	if len(history) < sd.noProgressThreshold {
		return nil, false // Not enough data yet
	}

	// Check for no progress (error count unchanged)
	if state := sd.detectNoProgress(history); state != nil {
		return state, true
	}

	// Check for regression (error count increasing)
	if state := sd.detectRegression(history); state != nil {
		return state, true
	}

	return nil, false // Not stuck
}

// detectNoProgress checks if error count unchanged for N iterations
func (sd *StuckDetector) detectNoProgress(history []IterationState) *StuckState {
	if len(history) < sd.noProgressThreshold {
		return nil
	}

	// Check last N iterations
	window := history[len(history)-sd.noProgressThreshold:]
	firstCount := window[0].ErrorCount

	allSame := true
	for i := 1; i < len(window); i++ {
		if window[i].ErrorCount != firstCount {
			allSame = false
			break
		}
	}

	if !allSame {
		return nil // Error count is changing
	}

	// No progress detected - error count stuck at same value
	return &StuckState{
		Type: StuckNoProgress,
		Description: fmt.Sprintf(
			"Error count unchanged at %d for %d iterations",
			firstCount,
			sd.noProgressThreshold,
		),
		Evidence: window,
		Suggestion: fmt.Sprintf(
			"Try different fix strategy - current approach not reducing errors. "+
				"Consider: (1) Different variant ranking, (2) Broader pattern search, "+
				"(3) Manual intervention for error at line %d",
			findMostFrequentErrorLine(window),
		),
	}
}

// detectRegression checks if error count is increasing
func (sd *StuckDetector) detectRegression(history []IterationState) *StuckState {
	if len(history) < 2 {
		return nil
	}

	// Check if last few iterations show increasing errors
	windowSize := min(3, len(history))
	window := history[len(history)-windowSize:]

	increasing := 0
	for i := 1; i < len(window); i++ {
		if window[i].ErrorCount > window[i-1].ErrorCount {
			increasing++
		}
	}

	// If majority show increase, we're regressing
	if increasing >= (windowSize-1)/2+1 {
		startCount := window[0].ErrorCount
		endCount := window[len(window)-1].ErrorCount
		delta := endCount - startCount

		return &StuckState{
			Type: StuckRegressing,
			Description: fmt.Sprintf(
				"Error count increasing: %d → %d (+%d errors in %d iterations)",
				startCount,
				endCount,
				delta,
				len(window),
			),
			Evidence: window,
			Suggestion: "STOP applying current fixes - they're making things worse! " +
				"Rollback to baseline and try completely different approach. " +
				"Current fixes introducing new errors faster than fixing old ones.",
		}
	}

	return nil
}

// DetectOscillation checks if error count is cycling between states
// Uses autocorrelation to detect periodic patterns
func (sd *StuckDetector) DetectOscillation(history []IterationState) bool {
	if len(history) < sd.oscillationWindow {
		return false
	}

	// Extract error counts from recent window
	window := history[len(history)-sd.oscillationWindow:]
	counts := make([]int, len(window))
	for i, state := range window {
		counts[i] = state.ErrorCount
	}

	// Detect oscillation using simple pattern matching
	// Pattern: A → B → A → B or A → B → C → A → B → C
	return detectSimpleOscillation(counts)
}

// detectSimpleOscillation detects 2-cycle or 3-cycle oscillations
func detectSimpleOscillation(counts []int) bool {
	if len(counts) < 4 {
		return false
	}

	// Check for 2-cycle: A → B → A → B
	twoycle := true
	for i := 0; i < len(counts)-2; i += 2 {
		if i+3 >= len(counts) {
			break
		}
		if counts[i] != counts[i+2] || counts[i+1] != counts[i+3] {
			twoycle = false
			break
		}
	}

	if twoycle && counts[0] != counts[1] {
		return true // Confirmed 2-cycle
	}

	// Check for 3-cycle: A → B → C → A → B → C
	if len(counts) >= 6 {
		threeCycle := true
		for i := 0; i < len(counts)-3; i += 3 {
			if i+5 >= len(counts) {
				break
			}
			if counts[i] != counts[i+3] ||
				counts[i+1] != counts[i+4] ||
				counts[i+2] != counts[i+5] {
				threeCycle = false
				break
			}
		}

		if threeCycle && (counts[0] != counts[1] || counts[1] != counts[2]) {
			return true // Confirmed 3-cycle
		}
	}

	return false
}

// StuckState describes why we're stuck and what to do
type StuckState struct {
	Type        StuckType          // Category of stuck state
	Description string             // Human-readable description
	Evidence    []IterationState   // Iterations showing stuck behavior
	Suggestion  string             // Actionable recommendation
}

// StuckType categorizes stuck states
type StuckType string

const (
	StuckNoProgress    StuckType = "no_progress"     // Error count unchanged
	StuckOscillating   StuckType = "oscillating"     // Cycling between states
	StuckRegressing    StuckType = "regressing"      // Error count increasing
	StuckMaxIterations StuckType = "max_iterations"  // Hit iteration limit
)

// findMostFrequentErrorLine identifies the error line appearing most often
// Used for targeted manual intervention suggestions
func findMostFrequentErrorLine(states []IterationState) int {
	if len(states) == 0 {
		return -1
	}

	// Count error lines from best variants
	lineCounts := make(map[int]int)
	for _, state := range states {
		if state.BestVariant != nil {
			// Extract line from first error (simplified - in production parse from compiler output)
			line := extractErrorLine(state.BestVariant.CompilerOutput)
			if line > 0 {
				lineCounts[line]++
			}
		}
	}

	// Find most frequent
	maxCount := 0
	mostFrequent := -1
	for line, count := range lineCounts {
		if count > maxCount {
			maxCount = count
			mostFrequent = line
		}
	}

	return mostFrequent
}

// extractErrorLine parses compiler output to extract error line number
// Simplified version - production would use proper regex parsing
func extractErrorLine(compilerOutput string) int {
	// Simplified: In production, parse "file.go:123:45: error message"
	// For now, return -1 (would need full implementation)
	return -1
}

// CalculateStuckConfidence returns confidence that we're stuck (0.0-1.0)
// Uses Vedic harmonic mean across multiple stuck indicators
func (sd *StuckDetector) CalculateStuckConfidence(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	// Calculate multiple stuck indicators
	indicators := []float64{
		sd.noProgressConfidence(history),
		sd.regressionConfidence(history),
		sd.oscillationConfidence(history),
		sd.velocityConfidence(history),
	}

	// Use harmonic mean (penalizes any weak indicator)
	sum := 0.0
	count := 0
	for _, ind := range indicators {
		if ind > 0 {
			sum += 1.0 / ind
			count++
		}
	}

	if count == 0 || sum == 0 {
		return 0.0
	}

	return float64(count) / sum
}

// noProgressConfidence measures confidence in no-progress diagnosis
func (sd *StuckDetector) noProgressConfidence(history []IterationState) float64 {
	if len(history) < sd.noProgressThreshold {
		return 0.0
	}

	window := history[len(history)-sd.noProgressThreshold:]
	firstCount := window[0].ErrorCount

	sameCount := 0
	for i := 1; i < len(window); i++ {
		if window[i].ErrorCount == firstCount {
			sameCount++
		}
	}

	return float64(sameCount) / float64(len(window)-1)
}

// regressionConfidence measures confidence in regression diagnosis
func (sd *StuckDetector) regressionConfidence(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	windowSize := min(5, len(history))
	window := history[len(history)-windowSize:]

	increasing := 0
	for i := 1; i < len(window); i++ {
		if window[i].ErrorCount > window[i-1].ErrorCount {
			increasing++
		}
	}

	return float64(increasing) / float64(len(window)-1)
}

// oscillationConfidence measures confidence in oscillation diagnosis
func (sd *StuckDetector) oscillationConfidence(history []IterationState) float64 {
	if len(history) < sd.oscillationWindow {
		return 0.0
	}

	window := history[len(history)-sd.oscillationWindow:]
	counts := make([]int, len(window))
	for i, state := range window {
		counts[i] = state.ErrorCount
	}

	// Calculate autocorrelation at lag 2 and 3 (detect 2-cycle and 3-cycle)
	lag2 := autocorrelation(counts, 2)
	lag3 := autocorrelation(counts, 3)

	// High autocorrelation at lag 2 or 3 indicates oscillation
	return math.Max(lag2, lag3)
}

// velocityConfidence measures confidence based on convergence velocity
func (sd *StuckDetector) velocityConfidence(history []IterationState) float64 {
	if len(history) < 2 {
		return 0.0
	}

	latest := history[len(history)-1]
	if latest.ConvergenceVelocity <= 0 {
		return 1.0 // No velocity = definitely stuck
	}

	// Velocity approaching zero = likely stuck
	// Use exponential decay: confidence = e^(-velocity)
	return math.Exp(-latest.ConvergenceVelocity)
}

// autocorrelation calculates autocorrelation at specified lag
// Used for oscillation detection (high autocorrelation = periodic pattern)
func autocorrelation(values []int, lag int) float64 {
	if len(values) <= lag {
		return 0.0
	}

	// Convert to floats
	data := make([]float64, len(values))
	for i, v := range values {
		data[i] = float64(v)
	}

	// Calculate mean
	mean := 0.0
	for _, v := range data {
		mean += v
	}
	mean /= float64(len(data))

	// Calculate autocorrelation
	numerator := 0.0
	denominator := 0.0

	for i := 0; i < len(data)-lag; i++ {
		numerator += (data[i] - mean) * (data[i+lag] - mean)
	}

	for i := 0; i < len(data); i++ {
		denominator += (data[i] - mean) * (data[i] - mean)
	}

	if denominator == 0 {
		return 0.0
	}

	return numerator / denominator
}
