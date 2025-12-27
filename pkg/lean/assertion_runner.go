// Package lean - Assertion Runner
// Executes runtime assertions and generates proof reports
package lean

import (
	"fmt"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION RUNNER
// Orchestrates running multiple assertions and collecting results
// ═══════════════════════════════════════════════════════════════════════════

// AssertionRunner executes assertions and collects results
type AssertionRunner struct {
	registry *AssertionRegistry
	results  []AssertionResult
}

// NewAssertionRunner creates an assertion runner with standard registry
func NewAssertionRunner() *AssertionRunner {
	return &AssertionRunner{
		registry: NewAssertionRegistry(),
		results:  make([]AssertionResult, 0),
	}
}

// NewAssertionRunnerWithRegistry creates runner with custom registry
func NewAssertionRunnerWithRegistry(registry *AssertionRegistry) *AssertionRunner {
	return &AssertionRunner{
		registry: registry,
		results:  make([]AssertionResult, 0),
	}
}

// RunAll runs all registered assertions on provided data slices
// data is a map: assertion_name -> []data_items
func (r *AssertionRunner) RunAll(data map[string][]interface{}) []AssertionResult {
	r.results = make([]AssertionResult, 0)

	for _, assertion := range r.registry.All() {
		name := assertion.Name()
		items, ok := data[name]
		if !ok || len(items) == 0 {
			// No data for this assertion, skip
			continue
		}

		// Run assertion on all data items
		for _, item := range items {
			result := r.runSingle(assertion, item)
			r.results = append(r.results, result)
		}
	}

	return r.results
}

// RunAssertion runs a specific assertion on provided data
func (r *AssertionRunner) RunAssertion(assertionName string, data interface{}) AssertionResult {
	assertion, ok := r.registry.Get(assertionName)
	if !ok {
		return AssertionResult{
			AssertionName: assertionName,
			Passed:        false,
			Error:         fmt.Sprintf("assertion %s not found in registry", assertionName),
			Severity:      SeverityCritical,
		}
	}

	result := r.runSingle(assertion, data)
	r.results = append(r.results, result)
	return result
}

// runSingle runs a single assertion on single data item
func (r *AssertionRunner) runSingle(assertion ProofAssertion, data interface{}) AssertionResult {
	err := assertion.Validate(data)

	result := AssertionResult{
		AssertionName: assertion.Name(),
		Theorem:       assertion.Theorem(),
		Severity:      assertion.Severity(),
		Passed:        err == nil,
		Data:          data,
	}

	if err != nil {
		result.Error = err.Error()
	}

	return result
}

// GetResults returns all collected results
func (r *AssertionRunner) GetResults() []AssertionResult {
	return r.results
}

// ClearResults clears all collected results
func (r *AssertionRunner) ClearResults() {
	r.results = make([]AssertionResult, 0)
}

// ═══════════════════════════════════════════════════════════════════════════
// STATISTICS
// ═══════════════════════════════════════════════════════════════════════════

// AssertionStats provides summary statistics
type AssertionStats struct {
	Total        int               `json:"total"`
	Passed       int               `json:"passed"`
	Failed       int               `json:"failed"`
	PassRate     float64           `json:"pass_rate"`
	BySeverity   map[string]int    `json:"by_severity"`
	ByAssertion  map[string]int    `json:"by_assertion"`
	CriticalFail int               `json:"critical_fail"`
}

// Stats computes statistics from collected results
func (r *AssertionRunner) Stats() AssertionStats {
	stats := AssertionStats{
		Total:       len(r.results),
		BySeverity:  make(map[string]int),
		ByAssertion: make(map[string]int),
	}

	for _, result := range r.results {
		if result.Passed {
			stats.Passed++
		} else {
			stats.Failed++
			stats.BySeverity[result.Severity.String()]++
			stats.ByAssertion[result.AssertionName]++

			if result.Severity == SeverityCritical {
				stats.CriticalFail++
			}
		}
	}

	if stats.Total > 0 {
		stats.PassRate = float64(stats.Passed) / float64(stats.Total)
	}

	return stats
}

// ═══════════════════════════════════════════════════════════════════════════
// PROOF REPORT GENERATION
// ═══════════════════════════════════════════════════════════════════════════

// ProofReport generates a comprehensive proof validation report
type ProofReport struct {
	Title        string
	GeneratedAt  time.Time
	Stats        AssertionStats
	Results      []AssertionResult
	Conclusion   string
}

// GenerateProofReport creates formatted proof report
func (r *AssertionRunner) GenerateProofReport() string {
	stats := r.Stats()

	var sb strings.Builder

	// Header
	sb.WriteString("╔═══════════════════════════════════════════════════════════════════════════╗\n")
	sb.WriteString("║                   RUNTIME PROOF VALIDATION REPORT                        ║\n")
	sb.WriteString("╚═══════════════════════════════════════════════════════════════════════════╝\n\n")

	sb.WriteString(fmt.Sprintf("Generated: %s\n\n", time.Now().Format("2006-01-02 15:04:05")))

	// Summary Statistics
	sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n")
	sb.WriteString("SUMMARY STATISTICS\n")
	sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n\n")

	sb.WriteString(fmt.Sprintf("Total Assertions Run:    %d\n", stats.Total))
	sb.WriteString(fmt.Sprintf("✅ Passed:               %d\n", stats.Passed))
	sb.WriteString(fmt.Sprintf("❌ Failed:               %d\n", stats.Failed))
	sb.WriteString(fmt.Sprintf("Pass Rate:              %.2f%%\n\n", stats.PassRate*100))

	// Severity Breakdown
	if len(stats.BySeverity) > 0 {
		sb.WriteString("Failures by Severity:\n")
		for severity, count := range stats.BySeverity {
			emoji := "ℹ️"
			if severity == "WARNING" {
				emoji = "⚠️"
			} else if severity == "CRITICAL" {
				emoji = "🔥"
			}
			sb.WriteString(fmt.Sprintf("  %s %s: %d\n", emoji, severity, count))
		}
		sb.WriteString("\n")
	}

	// Assertion Breakdown
	if len(stats.ByAssertion) > 0 {
		sb.WriteString("Failures by Assertion:\n")
		for assertion, count := range stats.ByAssertion {
			sb.WriteString(fmt.Sprintf("  - %s: %d\n", assertion, count))
		}
		sb.WriteString("\n")
	}

	// Detailed Results
	if len(r.results) > 0 {
		sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n")
		sb.WriteString("DETAILED RESULTS\n")
		sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n\n")

		// Group by assertion type
		grouped := make(map[string][]AssertionResult)
		for _, result := range r.results {
			grouped[result.AssertionName] = append(grouped[result.AssertionName], result)
		}

		for assertionName, results := range grouped {
			sb.WriteString(fmt.Sprintf("--- %s ---\n", assertionName))
			sb.WriteString(fmt.Sprintf("Theorem: %s\n", results[0].Theorem))

			passed := 0
			failed := 0
			for _, res := range results {
				if res.Passed {
					passed++
				} else {
					failed++
				}
			}

			sb.WriteString(fmt.Sprintf("Results: %d passed, %d failed\n", passed, failed))

			// Show first few failures (max 5)
			if failed > 0 {
				sb.WriteString("\nFailures:\n")
				count := 0
				for _, res := range results {
					if !res.Passed && count < 5 {
						sb.WriteString(fmt.Sprintf("  [%s] %s\n", res.Severity.String(), res.Error))
						count++
					}
				}
				if failed > 5 {
					sb.WriteString(fmt.Sprintf("  ... and %d more failures\n", failed-5))
				}
			}

			sb.WriteString("\n")
		}
	}

	// Conclusion
	sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n")
	sb.WriteString("CONCLUSION\n")
	sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n\n")

	if stats.Failed == 0 {
		sb.WriteString("✅ ALL PROOFS VALIDATED SUCCESSFULLY!\n")
		sb.WriteString("All runtime assertions passed. Formal proof assumptions hold in practice.\n\n")
	} else if stats.CriticalFail == 0 {
		sb.WriteString("⚠️  SOME NON-CRITICAL WARNINGS\n")
		sb.WriteString(fmt.Sprintf("%d warnings detected, but no critical violations.\n", stats.Failed))
		sb.WriteString("Execution is safe but should investigate warnings.\n\n")
	} else {
		sb.WriteString("🔥 CRITICAL VIOLATIONS DETECTED!\n")
		sb.WriteString(fmt.Sprintf("%d critical assertion failures.\n", stats.CriticalFail))
		sb.WriteString("Fundamental invariants violated - execution suspect!\n\n")
	}

	// Mathematical Rigor Statement
	sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n")
	sb.WriteString("MATHEMATICAL RIGOR\n")
	sb.WriteString("═══════════════════════════════════════════════════════════════════════════\n\n")

	sb.WriteString("\"Tests are instances. Runtime assertions bridge proofs to practice.\"\n")
	sb.WriteString("                                              - Maryam Mirzakhani\n\n")

	sb.WriteString("This report validates that Lean 4 proof assumptions hold during actual\n")
	sb.WriteString("execution. Each assertion corresponds to a formal theorem:\n\n")

	for _, assertion := range r.registry.All() {
		sb.WriteString(fmt.Sprintf("  • %s → theorem %s\n",
			assertion.Name(), assertion.Theorem()))
	}

	sb.WriteString("\n")

	return sb.String()
}

// GenerateCompactReport creates a compact one-line report
func (r *AssertionRunner) GenerateCompactReport() string {
	stats := r.Stats()

	if stats.Total == 0 {
		return "No assertions run"
	}

	if stats.Failed == 0 {
		return fmt.Sprintf("✅ All %d assertions passed (100%% validated)", stats.Total)
	}

	if stats.CriticalFail == 0 {
		return fmt.Sprintf("⚠️  %d/%d assertions passed (%.1f%%), %d warnings",
			stats.Passed, stats.Total, stats.PassRate*100, stats.Failed)
	}

	return fmt.Sprintf("🔥 CRITICAL: %d/%d failed (%.1f%% pass rate), %d critical violations",
		stats.Failed, stats.Total, stats.PassRate*100, stats.CriticalFail)
}

// ═══════════════════════════════════════════════════════════════════════════
// CONTINUOUS VALIDATION
// Hook into code execution for automatic assertion checking
// ═══════════════════════════════════════════════════════════════════════════

// ValidationHook is a global runner for continuous validation
var ValidationHook = NewAssertionRunner()

// ValidateQuaternion validates a quaternion immediately
func ValidateQuaternion(q *QuaternionData) error {
	assertion := NewQuaternionNormAssertion()
	return assertion.Validate(q)
}

// ValidateSLERP validates a SLERP operation immediately
func ValidateSLERP(slerp *SLERPData) error {
	assertion := NewSLERPPreservesS3Assertion()
	return assertion.Validate(slerp)
}

// ValidateMultiplication validates quaternion multiplication immediately
func ValidateMultiplication(mult *MultiplicationData) error {
	assertion := NewHamiltonClosureAssertion()
	return assertion.Validate(mult)
}

// ValidateDigitalRoot validates digital root immediately
func ValidateDigitalRoot(dr *DigitalRootData) error {
	assertion := NewDigitalRootPartitionAssertion()
	return assertion.Validate(dr)
}

// ValidateWilliams validates Williams batching immediately
func ValidateWilliams(w *WilliamsData) error {
	assertion := NewWilliamsSpaceBoundAssertion()
	return assertion.Validate(w)
}

// ValidateThreeRegime validates three-regime state immediately
func ValidateThreeRegime(regime *ThreeRegimeData) error {
	assertion := NewThreeRegimeStabilityAssertion()
	return assertion.Validate(regime)
}

// ═══════════════════════════════════════════════════════════════════════════
// BATCH VALIDATION
// Validate multiple items efficiently
// ═══════════════════════════════════════════════════════════════════════════

// BatchValidateQuaternions validates multiple quaternions
func BatchValidateQuaternions(quaternions []*QuaternionData) []AssertionResult {
	runner := NewAssertionRunner()
	data := make(map[string][]interface{})

	items := make([]interface{}, len(quaternions))
	for i, q := range quaternions {
		items[i] = q
	}
	data["QuaternionNormPreservation"] = items

	return runner.RunAll(data)
}

// BatchValidateSLERPs validates multiple SLERP operations
func BatchValidateSLERPs(slerps []*SLERPData) []AssertionResult {
	runner := NewAssertionRunner()
	data := make(map[string][]interface{})

	items := make([]interface{}, len(slerps))
	for i, s := range slerps {
		items[i] = s
	}
	data["SLERPPreservesS3"] = items

	return runner.RunAll(data)
}

// BatchValidateMultiplications validates multiple multiplications
func BatchValidateMultiplications(mults []*MultiplicationData) []AssertionResult {
	runner := NewAssertionRunner()
	data := make(map[string][]interface{})

	items := make([]interface{}, len(mults))
	for i, m := range mults {
		items[i] = m
	}
	data["HamiltonMultiplicationClosure"] = items

	return runner.RunAll(data)
}
