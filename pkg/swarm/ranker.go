package swarm

import "sort"

// Ranker sorts and analyzes scored results
type Ranker struct{}

// NewRanker creates a new ranker
func NewRanker() *Ranker {
	return &Ranker{}
}

// RankByQuality sorts scored results by quality score (highest first)
func (r *Ranker) RankByQuality(scored []ScoredResult) []ScoredResult {
	// Make a copy to avoid mutating input
	ranked := make([]ScoredResult, len(scored))
	copy(ranked, scored)

	sort.Slice(ranked, func(i, j int) bool {
		return ranked[i].QualityScore > ranked[j].QualityScore
	})

	return ranked
}

// RankByTimbre ranks by specific timbre (for analysis)
func (r *Ranker) RankByTimbre(scored []ScoredResult, timbre string) []ScoredResult {
	// Make a copy
	ranked := make([]ScoredResult, len(scored))
	copy(ranked, scored)

	sort.Slice(ranked, func(i, j int) bool {
		scoreI := r.getTimbreScore(ranked[i].Scores, timbre)
		scoreJ := r.getTimbreScore(ranked[j].Scores, timbre)
		return scoreI > scoreJ
	})

	return ranked
}

// getTimbreScore extracts specific timbre score
func (r *Ranker) getTimbreScore(scores FiveTimbresBreakdown, timbre string) float64 {
	switch timbre {
	case "correctness", "Correctness":
		return scores.Correctness
	case "performance", "Performance":
		return scores.Performance
	case "reliability", "Reliability":
		return scores.Reliability
	case "synergy", "Synergy":
		return scores.Synergy
	case "elegance", "Elegance":
		return scores.Elegance
	default:
		return scores.HarmonicMean
	}
}

// FindParetoDominant finds Pareto-optimal results
// (not dominated on any timbre by another result)
func (r *Ranker) FindParetoDominant(scored []ScoredResult) []ScoredResult {
	if len(scored) == 0 {
		return []ScoredResult{}
	}

	pareto := make([]ScoredResult, 0)

	for i := range scored {
		isDominated := false

		// Check if result i is dominated by any other result
		for j := range scored {
			if i == j {
				continue
			}

			if r.dominates(scored[j].Scores, scored[i].Scores) {
				isDominated = true
				break
			}
		}

		if !isDominated {
			pareto = append(pareto, scored[i])
		}
	}

	return pareto
}

// dominates checks if scoreA dominates scoreB
// (better or equal on all dimensions, strictly better on at least one)
func (r *Ranker) dominates(scoreA, scoreB FiveTimbresBreakdown) bool {
	betterCount := 0
	equalCount := 0

	timbresA := []float64{
		scoreA.Correctness,
		scoreA.Performance,
		scoreA.Reliability,
		scoreA.Synergy,
		scoreA.Elegance,
	}

	timbresB := []float64{
		scoreB.Correctness,
		scoreB.Performance,
		scoreB.Reliability,
		scoreB.Synergy,
		scoreB.Elegance,
	}

	for i := range timbresA {
		if timbresA[i] > timbresB[i] {
			betterCount++
		} else if timbresA[i] == timbresB[i] {
			equalCount++
		} else {
			// scoreA is worse on this dimension
			return false
		}
	}

	// Dominates if better on at least one dimension
	// and not worse on any
	return betterCount > 0
}

// RankByErrorReduction ranks by absolute error reduction
func (r *Ranker) RankByErrorReduction(scored []ScoredResult) []ScoredResult {
	ranked := make([]ScoredResult, len(scored))
	copy(ranked, scored)

	sort.Slice(ranked, func(i, j int) bool {
		reductionI := ranked[i].Result.ErrorsBefore - ranked[i].Result.ErrorsAfter
		reductionJ := ranked[j].Result.ErrorsBefore - ranked[j].Result.ErrorsAfter
		return reductionI > reductionJ
	})

	return ranked
}

// RankByCompilationTime ranks by fastest compilation
func (r *Ranker) RankByCompilationTime(scored []ScoredResult) []ScoredResult {
	ranked := make([]ScoredResult, len(scored))
	copy(ranked, scored)

	sort.Slice(ranked, func(i, j int) bool {
		return ranked[i].Result.CompilationTime < ranked[j].Result.CompilationTime
	})

	return ranked
}

// RankByConfidence ranks by pattern confidence
func (r *Ranker) RankByConfidence(scored []ScoredResult) []ScoredResult {
	ranked := make([]ScoredResult, len(scored))
	copy(ranked, scored)

	sort.Slice(ranked, func(i, j int) bool {
		return ranked[i].Result.Confidence > ranked[j].Result.Confidence
	})

	return ranked
}
