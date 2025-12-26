package swarm

import (
	"math"

)

// FiveTimbresScorer calculates quality using Five Timbres methodology
type FiveTimbresScorer struct {
	weights FiveTimbresWeights
}

// NewFiveTimbresScorer creates scorer with default equal weights
func NewFiveTimbresScorer() *FiveTimbresScorer {
	return &FiveTimbresScorer{
		weights: FiveTimbresWeights{
			Correctness: 1.0,
			Performance: 1.0,
			Reliability: 1.0,
			Synergy:     1.0,
			Elegance:    1.0,
		},
	}
}

// NewFiveTimbresCustomWeights creates scorer with custom weights
func NewFiveTimbresCustomWeights(weights FiveTimbresWeights) *FiveTimbresScorer {
	return &FiveTimbresScorer{weights: weights}
}

// ScoreResult calculates Five Timbres quality score
func (fts *FiveTimbresScorer) ScoreResult(
	result *FixResult,
	baselineErrors int,
) (float64, FiveTimbresBreakdown, error) {
	// Calculate each timbre
	correctness := fts.calculateCorrectness(result, baselineErrors)
	performance := fts.calculatePerformance(result)
	reliability := fts.calculateReliability(result)
	synergy := fts.calculateSynergy(result)
	elegance := fts.calculateElegance(result)

	// Apply weights
	weightedScores := []float64{
		correctness * fts.weights.Correctness,
		performance * fts.weights.Performance,
		reliability * fts.weights.Reliability,
		synergy * fts.weights.Synergy,
		elegance * fts.weights.Elegance,
	}

	// Harmonic mean (penalizes weakness!)
	quality := HarmonicMean(weightedScores)

	breakdown := FiveTimbresBreakdown{
		Correctness:  correctness,
		Performance:  performance,
		Reliability:  reliability,
		Synergy:      synergy,
		Elegance:     elegance,
		HarmonicMean: quality,
	}

	return quality, breakdown, nil
}

// calculateCorrectness measures error reduction ratio
func (fts *FiveTimbresScorer) calculateCorrectness(result *FixResult, baseline int) float64 {
	// If fix didn't succeed, correctness = 0
	if !result.Success {
		return 0.0
	}

	// If no baseline errors, perfect score
	if baseline == 0 {
		return 1.0
	}

	// Correctness = errors_reduced / baseline_errors
	errorsReduced := baseline - result.ErrorsAfter
	if errorsReduced < 0 {
		// Fix made things worse!
		return 0.0
	}

	score := float64(errorsReduced) / float64(baseline)
	return clamp(score, 0.0, 1.0)
}

// calculatePerformance measures compilation speed
func (fts *FiveTimbresScorer) calculatePerformance(result *FixResult) float64 {
	// Performance = 1.0 if compilation_time < 5s, scale down linearly
	targetTime := 5.0 // seconds
	actualTime := result.CompilationTime.Seconds()

	if actualTime <= 0 {
		// No compilation time recorded (likely failed)
		return 0.0
	}

	if actualTime <= targetTime {
		return 1.0
	}

	// Linear decay: score = target / actual
	// e.g., 10s compile = 5/10 = 0.5
	score := targetTime / actualTime
	return clamp(score, 0.0, 1.0)
}

// calculateReliability measures stability (no new errors introduced)
func (fts *FiveTimbresScorer) calculateReliability(result *FixResult) float64 {
	// Reliability = 1 - (new_errors / errors_fixed)
	errorsFixed := result.ErrorsBefore - result.ErrorsAfter

	if errorsFixed <= 0 {
		// Didn't fix any errors
		return 0.0
	}

	newErrorCount := len(result.NewErrors)
	if newErrorCount == 0 {
		// Perfect! Fixed errors without introducing new ones
		return 1.0
	}

	// Penalize new errors proportionally
	penalty := float64(newErrorCount) / float64(errorsFixed)
	score := 1.0 - penalty

	return clamp(score, 0.0, 1.0)
}

// calculateSynergy measures contextual fit
func (fts *FiveTimbresScorer) calculateSynergy(result *FixResult) float64 {
	// Synergy = how well fix fits into existing codebase
	// Use pattern confidence as primary indicator
	// Higher confidence = better pattern match = better synergy

	baseScore := result.Confidence

	// Bonus: fewer files modified = more focused fix = better synergy
	// Single-file fixes get bonus
	if len(result.FilesModified) == 1 {
		baseScore = math.Min(1.0, baseScore+0.05)
	}

	return clamp(baseScore, 0.0, 1.0)
}

// calculateElegance measures code quality
func (fts *FiveTimbresScorer) calculateElegance(result *FixResult) float64 {
	// Elegance heuristics:
	// - Shorter fixes preferred (fewer lines changed)
	// - Single-file changes preferred
	// - Clear fix descriptions

	score := 0.85 // Base elegance score

	// Shorter fixes are more elegant
	if result.LinesChanged <= 5 {
		score += 0.10
	} else if result.LinesChanged <= 20 {
		score += 0.05
	}

	// Single-file fixes are more elegant
	if len(result.FilesModified) == 1 {
		score += 0.05
	} else if len(result.FilesModified) > 3 {
		score -= 0.10
	}

	return clamp(score, 0.0, 1.0)
}

// clamp restricts value to [min, max] range
func clamp(value, min, max float64) float64 {
	if value < min {
		return min
	}
	if value > max {
		return max
	}
	return value
}
