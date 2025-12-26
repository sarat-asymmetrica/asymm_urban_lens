// Package verification implements compilation verification and regression detection
//
// Compilation Verifier: Main verification engine
// Author: Agent 4.1 (Dr. Liam O'Connor - Formal Verification, Oxford)
// Created: 2025-11-07
// Ported: 2025-12-26 (Urban Lens Integration)
//
// This verifier runs compilation and validates that applied fixes actually improve things.
// It uses Vedic principles (digital root, harmonic mean) for quality scoring.
package verification

import (
	"context"
	"fmt"
	"time"

	"github.com/asymm_urbanlens/urbanlens/pkg/reasoning"
)

// CompilationVerifier runs compiler and validates results
type CompilationVerifier struct {
	language       string
	projectPath    string
	timeout        time.Duration
	buildRunner    *BuildRunner
	parser         *OutputParser
	regDetector    *RegressionDetector
	cache          *VerificationCache
	useCache       bool
	strictMode     bool
}

// NewCompilationVerifier creates verifier for a project
func NewCompilationVerifier(projectPath, language string) *CompilationVerifier {
	return &CompilationVerifier{
		language:     language,
		projectPath:  projectPath,
		timeout:      5 * time.Minute,
		buildRunner:  NewBuildRunner(5 * time.Minute),
		parser:       NewOutputParser(language),
		regDetector:  NewRegressionDetector(false), // Normal mode by default
		cache:        NewVerificationCache(),
		useCache:     true,
		strictMode:   false,
	}
}

// WithTimeout sets custom timeout
func (cv *CompilationVerifier) WithTimeout(timeout time.Duration) *CompilationVerifier {
	cv.timeout = timeout
	cv.buildRunner = NewBuildRunner(timeout)
	return cv
}

// WithStrictMode enables strict regression detection (warnings = regressions)
func (cv *CompilationVerifier) WithStrictMode(strict bool) *CompilationVerifier {
	cv.strictMode = strict
	cv.regDetector = NewRegressionDetector(strict)
	return cv
}

// WithCache enables/disables caching
func (cv *CompilationVerifier) WithCache(useCache bool) *CompilationVerifier {
	cv.useCache = useCache
	return cv
}

// VerifyFix runs compilation and checks if fix improved things
func (cv *CompilationVerifier) VerifyFix(
	ctx context.Context,
	beforeErrors []reasoning.CompilationError,
	appliedFix interface{},
) (*VerificationResult, error) {
	// Check cache if enabled
	if cv.useCache {
		hash, err := CalculateFileHashFast(cv.projectPath)
		if err == nil {
			if cached, exists := cv.cache.Get(hash); exists {
				return cached, nil
			}
		}
	}

	// Run compiler
	buildOutput, err := cv.buildRunner.RunBuild(ctx, cv.projectPath, cv.language)
	if err != nil {
		return nil, fmt.Errorf("build execution failed: %w", err)
	}

	// Parse errors from output
	afterErrors, err := cv.parser.ParseOutput(buildOutput)
	if err != nil {
		return nil, fmt.Errorf("failed to parse compiler output: %w", err)
	}

	// Calculate diff
	diff := cv.parser.DiffErrors(beforeErrors, afterErrors)

	// Detect regressions
	regressions := cv.regDetector.DetectRegressions(diff)

	// Check if acceptable
	acceptable := cv.regDetector.IsAcceptable(diff.FixedCount, regressions)

	// Calculate quality score using Vedic harmonic mean
	qualityScore := cv.calculateQualityScore(diff, regressions, buildOutput)

	// Determine overall success
	success := cv.determineSuccess(diff, regressions, acceptable)

	result := &VerificationResult{
		Success:             success,
		ErrorsBefore:        len(beforeErrors),
		ErrorsAfter:         len(afterErrors),
		ErrorsFixed:         diff.FixedCount,
		NewErrorsIntroduced: diff.NewCount,
		Regressions:         regressions,
		CompilationTime:     buildOutput.Duration,
		CompilerOutput:      buildOutput.Stdout,
		Timestamp:           time.Now(),
		ErrorDiff:           diff,
		AcceptableTradeoff:  acceptable,
		QualityScore:        qualityScore,
	}

	// Cache result
	if cv.useCache {
		hash, err := CalculateFileHashFast(cv.projectPath)
		if err == nil {
			cv.cache.Set(hash, result)
		}
	}

	return result, nil
}

// VerifyCurrentState runs compilation without comparing to before state
// Useful for initial baseline verification
func (cv *CompilationVerifier) VerifyCurrentState(ctx context.Context) (*VerificationResult, error) {
	// Run compiler
	buildOutput, err := cv.buildRunner.RunBuild(ctx, cv.projectPath, cv.language)
	if err != nil {
		return nil, fmt.Errorf("build execution failed: %w", err)
	}

	// Parse errors
	errors, err := cv.parser.ParseOutput(buildOutput)
	if err != nil {
		return nil, fmt.Errorf("failed to parse compiler output: %w", err)
	}

	// No diff, just current state
	result := &VerificationResult{
		Success:             buildOutput.Success,
		ErrorsBefore:        0,
		ErrorsAfter:         len(errors),
		ErrorsFixed:         0,
		NewErrorsIntroduced: 0,
		Regressions:         []Regression{},
		CompilationTime:     buildOutput.Duration,
		CompilerOutput:      buildOutput.Stdout,
		Timestamp:           time.Now(),
		ErrorDiff:           nil,
		AcceptableTradeoff:  true,
		QualityScore:        cv.calculateBaselineQuality(errors, buildOutput),
	}

	return result, nil
}

// calculateQualityScore computes harmonic mean quality score (Five Timbres style)
func (cv *CompilationVerifier) calculateQualityScore(
	diff *ErrorDiff,
	regressions []Regression,
	buildOutput *BuildOutput,
) float64 {
	// Five dimensions of quality:
	// 1. Correctness: How many errors were fixed?
	// 2. Performance: How fast was compilation?
	// 3. Reliability: No critical regressions?
	// 4. Synergy: Net improvement (fixed - new)?
	// 5. Elegance: Acceptable tradeoff?

	// 1. Correctness (0.0 - 1.0)
	correctness := 0.0
	if diff.FixedCount > 0 {
		// Ratio of fixed to total before errors
		totalBefore := float64(diff.FixedCount + diff.UnchangedCount)
		if totalBefore > 0 {
			correctness = float64(diff.FixedCount) / totalBefore
		}
	}

	// 2. Performance (0.0 - 1.0)
	// Target: < 30s compilation
	performance := 1.0
	compileSeconds := buildOutput.Duration.Seconds()
	if compileSeconds > 30.0 {
		performance = 30.0 / compileSeconds
		if performance < 0.1 {
			performance = 0.1 // Minimum score
		}
	}

	// 3. Reliability (0.0 - 1.0)
	// Penalize critical regressions heavily
	reliability := 1.0
	regressionScore := cv.regDetector.CalculateRegressionScore(regressions)
	reliability = 1.0 - regressionScore
	if reliability < 0.0 {
		reliability = 0.0
	}

	// 4. Synergy (0.0 - 1.0)
	// Net improvement score
	synergy := 0.5 // Neutral if no change
	netImprovement := diff.FixedCount - diff.NewCount
	if netImprovement > 0 {
		// Positive improvement
		synergy = 0.5 + (0.5 * float64(netImprovement) / float64(diff.FixedCount+1))
	} else if netImprovement < 0 {
		// Negative impact
		synergy = 0.5 - (0.5 * float64(-netImprovement) / float64(diff.NewCount+1))
	}
	if synergy < 0.0 {
		synergy = 0.0
	}
	if synergy > 1.0 {
		synergy = 1.0
	}

	// 5. Elegance (0.0 - 1.0)
	// Acceptable tradeoff?
	elegance := 0.0
	if cv.regDetector.IsAcceptable(diff.FixedCount, regressions) {
		elegance = 1.0
	} else {
		// Partial credit based on severity
		elegance = 0.3 // Some credit for trying
	}

	// Use Vedic harmonic mean (penalizes weakness)
	scores := []float64{correctness, performance, reliability, synergy, elegance}
	harmonicMean := harmonicMean(scores)

	return harmonicMean
}

// calculateBaselineQuality computes quality for current state (no comparison)
func (cv *CompilationVerifier) calculateBaselineQuality(
	errors []reasoning.CompilationError,
	buildOutput *BuildOutput,
) float64 {
	// Simpler scoring for baseline
	// 1. Correctness: Does it compile?
	correctness := 0.0
	if buildOutput.Success {
		correctness = 1.0
	} else {
		// Partial credit based on error count
		// Fewer errors = higher score
		if len(errors) == 0 {
			correctness = 1.0
		} else if len(errors) < 5 {
			correctness = 0.7
		} else if len(errors) < 20 {
			correctness = 0.4
		} else {
			correctness = 0.1
		}
	}

	// 2. Performance
	performance := 1.0
	compileSeconds := buildOutput.Duration.Seconds()
	if compileSeconds > 30.0 {
		performance = 30.0 / compileSeconds
		if performance < 0.1 {
			performance = 0.1
		}
	}

	// Average of correctness and performance
	return (correctness + performance) / 2.0
}

// determineSuccess checks if verification succeeded
func (cv *CompilationVerifier) determineSuccess(
	diff *ErrorDiff,
	regressions []Regression,
	acceptable bool,
) bool {
	// Success if:
	// 1. Errors decreased OR stayed same
	// 2. No critical regressions
	// 3. Tradeoff is acceptable

	errorsDecreased := diff.FixedCount >= diff.NewCount

	// Check for critical regressions
	hasCritical := false
	for _, reg := range regressions {
		if reg.Severity == SeverityCritical {
			hasCritical = true
			break
		}
	}

	return errorsDecreased && !hasCritical && acceptable
}

// ClearCache clears verification cache
func (cv *CompilationVerifier) ClearCache() {
	cv.cache.Clear()
}

// GetCacheSize returns cache size
func (cv *CompilationVerifier) GetCacheSize() int {
	return cv.cache.Size()
}

// harmonicMean calculates harmonic mean of scores (Vedic quality metric)
// Formula: n / Σ(1/xᵢ)
// Penalizes weakness - one low score significantly lowers the result
func harmonicMean(scores []float64) float64 {
	if len(scores) == 0 {
		return 0.0
	}

	var reciprocalSum float64
	for _, score := range scores {
		if score <= 0 {
			// Handle zero/negative scores
			return 0.0
		}
		reciprocalSum += 1.0 / score
	}

	if reciprocalSum == 0 {
		return 0.0
	}

	return float64(len(scores)) / reciprocalSum
}
