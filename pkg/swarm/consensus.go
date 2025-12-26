package swarm

import (
	"fmt"

)

// ConsensusValidator ensures best fix meets quality thresholds
type ConsensusValidator struct {
	minQualityScore float64 // Minimum overall quality (default: PHI = 0.618)
	minCorrectness  float64 // Minimum error reduction (default: 0.50)
}

// NewConsensusValidator creates validator with PHI-based thresholds
func NewConsensusValidator() *ConsensusValidator {
	return &ConsensusValidator{
		minQualityScore: PHI - 1.0, // φ - 1 = 0.618 (golden ratio)
		minCorrectness:  0.50,                     // Must fix at least 50% of errors
	}
}

// NewConsensusCustomThresholds creates validator with custom thresholds
func NewConsensusCustomThresholds(minQuality, minCorrectness float64) *ConsensusValidator {
	return &ConsensusValidator{
		minQualityScore: minQuality,
		minCorrectness:  minCorrectness,
	}
}

// ValidateBest checks if best result is acceptable
func (cv *ConsensusValidator) ValidateBest(result *AggregatedResult) ValidationResult {
	if result == nil {
		return ValidationResult{
			Approved: false,
			Reason:   "No aggregated result provided",
			Suggestions: []string{
				"Re-run swarm with different patterns",
				"Increase K (number of variants)",
			},
		}
	}

	// No successful fixes
	if result.SuccessfulFixes == 0 {
		return ValidationResult{
			Approved: false,
			Reason:   fmt.Sprintf("No successful fixes (%d failures)", result.FailedFixes),
			Suggestions: []string{
				"Check if patterns match actual errors",
				"Try broader pattern categories",
				"Increase fix timeout",
				"Verify codebase is compilable baseline",
			},
		}
	}

	// No best result (shouldn't happen, but check anyway)
	if result.BestResult == nil {
		return ValidationResult{
			Approved: false,
			Reason:   "No best result identified despite successful fixes",
			Suggestions: []string{
				"Check aggregator logic",
				"Verify scorer is working correctly",
			},
		}
	}

	// Check quality threshold
	if result.BestScore < cv.minQualityScore {
		return ValidationResult{
			Approved: false,
			Reason: fmt.Sprintf(
				"Quality score %.3f below threshold %.3f (PHI-based)",
				result.BestScore,
				cv.minQualityScore,
			),
			Suggestions: []string{
				fmt.Sprintf("Current best variant: %d (pattern: %s)",
					result.BestResult.VariantID,
					result.BestResult.PatternName),
				"Try different fix patterns",
				"Combine multiple fix approaches",
				"Increase variant diversity (higher K)",
			},
		}
	}

	// Check correctness threshold
	best := result.BestResult
	errorsFixed := best.ErrorsBefore - best.ErrorsAfter
	correctness := 0.0
	if best.ErrorsBefore > 0 {
		correctness = float64(errorsFixed) / float64(best.ErrorsBefore)
	}

	if correctness < cv.minCorrectness {
		return ValidationResult{
			Approved: false,
			Reason: fmt.Sprintf(
				"Correctness %.1f%% below threshold %.1f%% (fixes %d/%d errors)",
				correctness*100.0,
				cv.minCorrectness*100.0,
				errorsFixed,
				best.ErrorsBefore,
			),
			Suggestions: []string{
				"Current fix is too partial",
				"Combine with other patterns to fix more errors",
				"Try more aggressive fix strategies",
			},
		}
	}

	// Check for excessive new errors
	if len(best.NewErrors) > 0 {
		newErrorRatio := float64(len(best.NewErrors)) / float64(errorsFixed)
		if newErrorRatio > 0.5 {
			return ValidationResult{
				Approved: false,
				Reason: fmt.Sprintf(
					"Introduces %d new errors while fixing %d (ratio: %.2f > 0.5)",
					len(best.NewErrors),
					errorsFixed,
					newErrorRatio,
				),
				Suggestions: []string{
					"Fix introduces too many new problems",
					"Try more conservative patterns",
					"Focus on single-error fixes first",
					"Review new errors for common cause",
				},
			}
		}
	}

	// All checks passed!
	return ValidationResult{
		Approved: true,
		Reason: fmt.Sprintf(
			"APPROVED: Quality %.3f (≥%.3f), Correctness %.1f%% (≥%.1f%%), "+
				"Fixes %d errors, %d new errors (ratio: %.2f)",
			result.BestScore,
			cv.minQualityScore,
			correctness*100.0,
			cv.minCorrectness*100.0,
			errorsFixed,
			len(best.NewErrors),
			safeRatio(len(best.NewErrors), errorsFixed),
		),
		Suggestions: []string{
			fmt.Sprintf("Apply variant %d using pattern '%s'",
				best.VariantID,
				best.PatternName),
		},
	}
}

// ValidateWithContext validates with additional context
func (cv *ConsensusValidator) ValidateWithContext(
	result *AggregatedResult,
	convergenceIteration int,
	maxIterations int,
) ValidationResult {
	// First do standard validation
	baseResult := cv.ValidateBest(result)

	// If already rejected, return with convergence context
	if !baseResult.Approved {
		baseResult.Suggestions = append(baseResult.Suggestions,
			fmt.Sprintf("Convergence: iteration %d/%d",
				convergenceIteration,
				maxIterations))
		return baseResult
	}

	// Check if we're near max iterations
	if convergenceIteration >= maxIterations-2 {
		// Near convergence limit - be more lenient
		if result.BestScore >= cv.minQualityScore*0.9 {
			return ValidationResult{
				Approved: true,
				Reason: fmt.Sprintf(
					"APPROVED (near convergence limit): Quality %.3f (≥%.3f with 10%% tolerance)",
					result.BestScore,
					cv.minQualityScore*0.9,
				),
				Suggestions: baseResult.Suggestions,
			}
		}
	}

	return baseResult
}

// safeRatio calculates ratio, handling division by zero
func safeRatio(numerator, denominator int) float64 {
	if denominator == 0 {
		return 0.0
	}
	return float64(numerator) / float64(denominator)
}
