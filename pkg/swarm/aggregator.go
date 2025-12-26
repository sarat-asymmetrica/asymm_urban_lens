package swarm

import (
	"fmt"
	"sort"
)

// Aggregator selects best fix from swarm results
type Aggregator struct {
	scorer *FiveTimbresScorer
}

// NewAggregator creates aggregator with default scorer
func NewAggregator() *Aggregator {
	return &Aggregator{
		scorer: NewFiveTimbresScorer(),
	}
}

// NewAggregatorWithScorer creates aggregator with custom scorer
func NewAggregatorWithScorer(scorer *FiveTimbresScorer) *Aggregator {
	return &Aggregator{scorer: scorer}
}

// AggregateResults processes all fix results and selects best
func (a *Aggregator) AggregateResults(
	results []*FixResult,
	baselineErrors int,
) (*AggregatedResult, error) {
	if len(results) == 0 {
		return &AggregatedResult{
			TotalCandidates: 0,
			SuccessfulFixes: 0,
			FailedFixes:     0,
			Recommendation:  "reject_all",
			Rationale:       "No results to aggregate",
		}, nil
	}

	// Step 1: Filter out failures (Success=false)
	successful := make([]*FixResult, 0)
	failed := 0

	for _, result := range results {
		if result.Success {
			successful = append(successful, result)
		} else {
			failed++
		}
	}

	// If no successful fixes, reject all
	if len(successful) == 0 {
		return &AggregatedResult{
			TotalCandidates: len(results),
			SuccessfulFixes: 0,
			FailedFixes:     failed,
			Recommendation:  "reject_all",
			Rationale:       fmt.Sprintf("All %d fix attempts failed compilation", len(results)),
		}, nil
	}

	// Step 2: Score each successful result using Five Timbres
	scoredResults := make([]ScoredResult, 0, len(successful))

	for _, result := range successful {
		quality, breakdown, err := a.scorer.ScoreResult(result, baselineErrors)
		if err != nil {
			return nil, fmt.Errorf("failed to score result variant %d: %w", result.VariantID, err)
		}

		scoredResults = append(scoredResults, ScoredResult{
			Result:       result,
			QualityScore: quality,
			Scores:       breakdown,
		})
	}

	// Step 3: Rank by quality score (highest first)
	sort.Slice(scoredResults, func(i, j int) bool {
		return scoredResults[i].QualityScore > scoredResults[j].QualityScore
	})

	// Step 4: Select best (highest score)
	best := scoredResults[0]

	// Step 5: Determine recommendation
	recommendation, rationale := a.makeRecommendation(best, baselineErrors)

	return &AggregatedResult{
		BestResult:      best.Result,
		BestScore:       best.QualityScore,
		AllScores:       scoredResults,
		TotalCandidates: len(results),
		SuccessfulFixes: len(successful),
		FailedFixes:     failed,
		Recommendation:  recommendation,
		Rationale:       rationale,
	}, nil
}

// makeRecommendation determines if best fix should be applied
func (a *Aggregator) makeRecommendation(best ScoredResult, baselineErrors int) (string, string) {
	const phiThreshold = 0.618 // Golden ratio - quality threshold

	// Check if quality meets threshold
	if best.QualityScore < phiThreshold {
		return "reject_all", fmt.Sprintf(
			"Best quality score %.3f is below PHI threshold %.3f. "+
				"Strongest weakness: %s (%.3f). Consider different approach.",
			best.QualityScore,
			phiThreshold,
			findWeakestTimbre(best.Scores),
			getWeakestScore(best.Scores),
		)
	}

	// Check if actually fixes errors
	if best.Result.ErrorsAfter >= baselineErrors {
		return "reject_all", fmt.Sprintf(
			"Best fix doesn't reduce errors (before: %d, after: %d). "+
				"Quality score %.3f insufficient despite passing threshold.",
			baselineErrors,
			best.Result.ErrorsAfter,
			best.QualityScore,
		)
	}

	// Check for new errors
	if len(best.Result.NewErrors) > 0 {
		newErrorRatio := float64(len(best.Result.NewErrors)) / float64(baselineErrors-best.Result.ErrorsAfter)
		if newErrorRatio > 0.3 {
			return "need_review", fmt.Sprintf(
				"Best fix introduces %d new errors while fixing %d (ratio: %.2f). "+
					"Quality score %.3f. Manual review recommended.",
				len(best.Result.NewErrors),
				baselineErrors-best.Result.ErrorsAfter,
				newErrorRatio,
				best.QualityScore,
			)
		}
	}

	// All checks passed - apply fix
	errorsFixed := baselineErrors - best.Result.ErrorsAfter
	return "apply", fmt.Sprintf(
		"Apply fix variant %d (quality: %.3f). "+
			"Fixes %d/%d errors (%.1f%%). "+
			"Pattern: %s (confidence: %.2f). "+
			"Timbres: C=%.2f P=%.2f R=%.2f S=%.2f E=%.2f",
		best.Result.VariantID,
		best.QualityScore,
		errorsFixed,
		baselineErrors,
		100.0*float64(errorsFixed)/float64(baselineErrors),
		best.Result.PatternName,
		best.Result.Confidence,
		best.Scores.Correctness,
		best.Scores.Performance,
		best.Scores.Reliability,
		best.Scores.Synergy,
		best.Scores.Elegance,
	)
}

// findWeakestTimbre identifies lowest-scoring dimension
func findWeakestTimbre(scores FiveTimbresBreakdown) string {
	timbres := map[string]float64{
		"Correctness": scores.Correctness,
		"Performance": scores.Performance,
		"Reliability": scores.Reliability,
		"Synergy":     scores.Synergy,
		"Elegance":    scores.Elegance,
	}

	weakest := "Unknown"
	minScore := 1.0

	for name, score := range timbres {
		if score < minScore {
			minScore = score
			weakest = name
		}
	}

	return weakest
}

// getWeakestScore returns lowest timbre score
func getWeakestScore(scores FiveTimbresBreakdown) float64 {
	min := scores.Correctness

	if scores.Performance < min {
		min = scores.Performance
	}
	if scores.Reliability < min {
		min = scores.Reliability
	}
	if scores.Synergy < min {
		min = scores.Synergy
	}
	if scores.Elegance < min {
		min = scores.Elegance
	}

	return min
}
