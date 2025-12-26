// Package lean - Proof Verifier
// Verifies Lean 4 proofs (mock mode for development without Lean installed)
package lean

import (
	"context"
	"fmt"
	"regexp"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// AI-ASSISTED VERIFICATION (Mock Mode)
// ═══════════════════════════════════════════════════════════════════════════

// AIClient interface for LLM-based verification simulation
type AIClient interface {
	// Generate sends a prompt and returns the response
	Generate(ctx context.Context, prompt string) (string, error)
}

// SimulateVerification uses AI to simulate Lean 4 verification
// This is a fallback when Lean is not installed
func SimulateVerification(code string, aiClient AIClient) (*VerificationResult, error) {
	start := time.Now()

	// Quick heuristic checks first
	result := &VerificationResult{
		Duration:    0,
		LeanVersion: "4.0.0-simulated",
	}

	// Check for obvious issues
	issues := quickLintCheck(code)
	if len(issues) > 0 {
		result.Valid = false
		result.Errors = issues
		result.Duration = time.Since(start)
		return result, nil
	}

	// If AI client available, use it for deeper analysis
	if aiClient != nil {
		prompt := buildVerificationPrompt(code)
		response, err := aiClient.Generate(context.Background(), prompt)
		if err != nil {
			// Fall back to basic validation
			result.Valid = !strings.Contains(code, "sorry")
			if !result.Valid {
				result.Errors = []string{"Proof incomplete (contains 'sorry')"}
			}
		} else {
			// Parse AI response
			parseAIVerification(response, result)
		}
	} else {
		// Basic validation without AI
		result.Valid = !strings.Contains(code, "sorry")
		if !result.Valid {
			result.Errors = []string{"Proof incomplete (contains 'sorry')"}
		}
	}

	result.Duration = time.Since(start)
	return result, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ENHANCED VERIFICATION
// ═══════════════════════════════════════════════════════════════════════════

// VerifyWithFeedback provides detailed feedback on proof
func VerifyWithFeedback(ctx context.Context, bridge Bridge, code string) (*DetailedVerificationResult, error) {
	// Run basic verification
	result, err := bridge.Verify(ctx, code)
	if err != nil {
		return nil, err
	}

	detailed := &DetailedVerificationResult{
		VerificationResult: *result,
		Suggestions:        []string{},
		MissingLemmas:      []string{},
		TacticHints:        []string{},
	}

	// Analyze errors and provide suggestions
	if !result.Valid {
		for _, errMsg := range result.Errors {
			suggestions := suggestFixForError(errMsg)
			detailed.Suggestions = append(detailed.Suggestions, suggestions...)
		}
	}

	// Check for common proof patterns that might be missing
	detailed.MissingLemmas = detectMissingLemmas(code)
	detailed.TacticHints = suggestNextTactics(code)

	return detailed, nil
}

// DetailedVerificationResult extends VerificationResult with helpful feedback
type DetailedVerificationResult struct {
	VerificationResult
	Suggestions   []string // How to fix errors
	MissingLemmas []string // Lemmas that might help
	TacticHints   []string // Next tactics to try
}

// ═══════════════════════════════════════════════════════════════════════════
// QUICK LINT CHECKS
// ═══════════════════════════════════════════════════════════════════════════

// quickLintCheck performs fast syntax checks
func quickLintCheck(code string) []string {
	var issues []string

	// Check for balanced parentheses
	if !balancedParens(code) {
		issues = append(issues, "Unbalanced parentheses")
	}

	// Check for theorem without proof
	if strings.Contains(code, "theorem") && !strings.Contains(code, ":= by") {
		issues = append(issues, "Theorem declared without proof")
	}

	// Check for unclosed proof blocks
	byCount := strings.Count(code, " by")
	// This is a simplification - real check would be more sophisticated
	if byCount > 0 {
		// Check if there's at least one tactic or sorry
		if !strings.Contains(code, "sorry") &&
			!strings.Contains(code, "exact") &&
			!strings.Contains(code, "intro") &&
			!strings.Contains(code, "simp") {
			issues = append(issues, "Proof body appears empty (no tactics found)")
		}
	}

	// Check for common typos
	typos := map[string]string{
		"theorm":   "theorem",
		"defn":     "def",
		"intros":   "intro",
		"exacts":   "exact",
		"refls":    "rfl",
		"sorries":  "sorry",
	}

	for typo, correct := range typos {
		if strings.Contains(code, typo) {
			issues = append(issues, fmt.Sprintf("Possible typo: '%s' (did you mean '%s'?)", typo, correct))
		}
	}

	// Check for invalid identifiers
	invalidIdPattern := regexp.MustCompile(`\b\d+[a-zA-Z]`)
	if invalidIdPattern.MatchString(code) {
		issues = append(issues, "Invalid identifier format (identifiers cannot start with digits)")
	}

	return issues
}

// balancedParens checks if parentheses are balanced
func balancedParens(code string) bool {
	count := 0
	for _, ch := range code {
		if ch == '(' {
			count++
		} else if ch == ')' {
			count--
			if count < 0 {
				return false
			}
		}
	}
	return count == 0
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR ANALYSIS & SUGGESTIONS
// ═══════════════════════════════════════════════════════════════════════════

// suggestFixForError analyzes error message and suggests fixes
func suggestFixForError(errMsg string) []string {
	suggestions := []string{}

	errLower := strings.ToLower(errMsg)

	// Type mismatch errors
	if strings.Contains(errLower, "type mismatch") {
		suggestions = append(suggestions,
			"Try using type coercion or conversion functions",
			"Check that all variables have the expected types",
			"Use #check to verify types of expressions",
		)
	}

	// Unknown identifier errors
	if strings.Contains(errLower, "unknown identifier") || strings.Contains(errLower, "not found") {
		suggestions = append(suggestions,
			"Check spelling of identifiers",
			"Make sure all variables are introduced with 'intro' or 'let'",
			"Verify that required imports are included",
		)
	}

	// Tactic failed errors
	if strings.Contains(errLower, "tactic") && strings.Contains(errLower, "failed") {
		suggestions = append(suggestions,
			"Try a different tactic (e.g., simp, ring, omega)",
			"Break down the goal into smaller steps",
			"Check if you need to introduce variables first",
		)
	}

	// Incomplete proof
	if strings.Contains(errLower, "sorry") {
		suggestions = append(suggestions,
			"Replace 'sorry' with actual proof steps",
			"Break the proof into lemmas if it's complex",
			"Use tactics like 'exact', 'apply', or 'constructor'",
		)
	}

	return suggestions
}

// detectMissingLemmas identifies potentially helpful lemmas
func detectMissingLemmas(code string) []string {
	lemmas := []string{}

	// Check for arithmetic operations
	if regexp.MustCompile(`\+|-|\*|/`).MatchString(code) {
		lemmas = append(lemmas, "ring", "omega", "linarith")
	}

	// Check for inequalities
	if regexp.MustCompile(`<|>|≤|≥`).MatchString(code) {
		lemmas = append(lemmas, "Nat.lt_trans", "Nat.le_trans", "Int.add_le_add")
	}

	// Check for existential proofs
	if strings.Contains(code, "∃") || strings.Contains(code, "Exists") {
		lemmas = append(lemmas, "Exists.intro", "use tactic")
	}

	// Check for universal quantification
	if strings.Contains(code, "∀") || strings.Contains(code, "forall") {
		lemmas = append(lemmas, "forall.intro", "intro tactic")
	}

	// Check for equality
	if strings.Contains(code, "=") {
		lemmas = append(lemmas, "rfl", "Eq.symm", "Eq.trans", "Eq.subst")
	}

	return lemmas
}

// suggestNextTactics suggests tactics based on current proof state
func suggestNextTactics(code string) []string {
	tactics := []string{}

	// If proof just started
	if strings.Count(code, "by") == 1 && strings.Count(code, "\n") < 5 {
		tactics = append(tactics, "intro - introduce variables")
	}

	// If there's a conjunction
	if strings.Contains(code, "∧") || strings.Contains(code, "And") {
		tactics = append(tactics, "constructor - split conjunction")
	}

	// If there's a disjunction
	if strings.Contains(code, "∨") || strings.Contains(code, "Or") {
		tactics = append(tactics, "left/right - choose disjunct")
	}

	// If there's an implication
	if strings.Contains(code, "→") {
		tactics = append(tactics, "intro - assume hypothesis")
	}

	// If doing induction
	if strings.Contains(code, "induction") {
		tactics = append(tactics, "Use inductive hypothesis 'ih'")
	}

	// If proving equality
	if strings.Contains(code, "= ") {
		tactics = append(tactics, "rfl - reflexivity", "simp - simplification", "ring - ring normalization")
	}

	return tactics
}

// ═══════════════════════════════════════════════════════════════════════════
// AI VERIFICATION HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// buildVerificationPrompt creates prompt for AI-based verification
func buildVerificationPrompt(code string) string {
	return fmt.Sprintf(`You are a Lean 4 theorem prover expert. Analyze this proof and determine if it's valid:

%s

Respond in this format:
VALID: [yes/no]
ERRORS: [list any errors, one per line]
WARNINGS: [list any warnings, one per line]
SUGGESTIONS: [list improvement suggestions, one per line]
`, code)
}

// parseAIVerification parses AI response into VerificationResult
func parseAIVerification(response string, result *VerificationResult) {
	lines := strings.Split(response, "\n")

	var currentSection string
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		// Detect sections
		if strings.HasPrefix(line, "VALID:") {
			validStr := strings.TrimSpace(strings.TrimPrefix(line, "VALID:"))
			result.Valid = strings.ToLower(validStr) == "yes"
			continue
		}

		if strings.HasPrefix(line, "ERRORS:") {
			currentSection = "errors"
			continue
		}

		if strings.HasPrefix(line, "WARNINGS:") {
			currentSection = "warnings"
			continue
		}

		if strings.HasPrefix(line, "SUGGESTIONS:") {
			currentSection = "suggestions"
			continue
		}

		// Add to current section
		switch currentSection {
		case "errors":
			if !strings.HasPrefix(line, "-") && !strings.HasPrefix(line, "*") {
				line = "- " + line
			}
			result.Errors = append(result.Errors, strings.TrimPrefix(strings.TrimPrefix(line, "- "), "* "))
		case "warnings":
			if !strings.HasPrefix(line, "-") && !strings.HasPrefix(line, "*") {
				line = "- " + line
			}
			result.Warnings = append(result.Warnings, strings.TrimPrefix(strings.TrimPrefix(line, "- "), "* "))
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// PROOF METRICS
// ═══════════════════════════════════════════════════════════════════════════

// ProofMetrics provides statistics about a proof
type ProofMetrics struct {
	LineCount      int      // Number of lines
	TacticCount    int      // Number of tactics used
	LemmaCount     int      // Number of lemmas referenced
	ComplexityScore float64 // Estimated complexity (0-1)
	UsedTactics    []string // List of tactics used
}

// AnalyzeProof computes metrics for a proof
func AnalyzeProof(code string) *ProofMetrics {
	metrics := &ProofMetrics{
		UsedTactics: []string{},
	}

	lines := strings.Split(code, "\n")
	metrics.LineCount = len(lines)

	// Count tactics
	tactics := []string{
		"intro", "exact", "apply", "rw", "simp", "ring", "omega",
		"constructor", "cases", "induction", "by_contra", "use",
		"left", "right", "split", "ext", "funext", "rfl",
	}

	tacticCounts := make(map[string]int)
	for _, tactic := range tactics {
		count := strings.Count(code, tactic)
		if count > 0 {
			metrics.TacticCount += count
			metrics.UsedTactics = append(metrics.UsedTactics, tactic)
			tacticCounts[tactic] = count
		}
	}

	// Count lemma references (rough heuristic)
	// Look for theorem/lemma names (capitalized or with dots)
	lemmaPattern := regexp.MustCompile(`\b([A-Z][a-zA-Z]*\.[a-zA-Z_]+|[A-Z][a-zA-Z_]+)\b`)
	lemmas := lemmaPattern.FindAllString(code, -1)
	metrics.LemmaCount = len(lemmas)

	// Compute complexity score
	// Based on: line count, tactic count, lemma usage, nesting depth
	complexity := 0.0
	complexity += float64(metrics.LineCount) * 0.01       // Lines contribute
	complexity += float64(metrics.TacticCount) * 0.05     // Tactics contribute more
	complexity += float64(metrics.LemmaCount) * 0.03      // Lemmas contribute
	complexity += float64(countNesting(code)) * 0.1       // Nesting contributes most

	// Normalize to 0-1 range (roughly)
	metrics.ComplexityScore = complexity / (complexity + 1.0)

	return metrics
}

// countNesting counts maximum nesting depth of proof blocks
func countNesting(code string) int {
	maxDepth := 0
	currentDepth := 0

	for _, line := range strings.Split(code, "\n") {
		// Increase depth on indentation or block starts
		if strings.Contains(line, "by") || strings.Contains(line, "with") {
			currentDepth++
		}

		// Track max
		if currentDepth > maxDepth {
			maxDepth = currentDepth
		}

		// Decrease depth on dedentation (rough heuristic)
		trimmed := strings.TrimLeft(line, " \t")
		if len(trimmed) > 0 && (trimmed[0] == '·' || strings.HasPrefix(trimmed, "|")) {
			// Bullet points or cases don't change depth, but track them
		}
	}

	return maxDepth
}

// ═══════════════════════════════════════════════════════════════════════════
// PROOF COMPARISON
// ═══════════════════════════════════════════════════════════════════════════

// CompareProofs compares two proofs of the same theorem
func CompareProofs(proof1, proof2 string) *ProofComparison {
	m1 := AnalyzeProof(proof1)
	m2 := AnalyzeProof(proof2)

	comparison := &ProofComparison{
		Proof1Metrics: m1,
		Proof2Metrics: m2,
	}

	// Determine which is simpler
	if m1.ComplexityScore < m2.ComplexityScore {
		comparison.SimplerProof = 1
		comparison.Recommendation = "Proof 1 is simpler (lower complexity score)"
	} else if m2.ComplexityScore < m1.ComplexityScore {
		comparison.SimplerProof = 2
		comparison.Recommendation = "Proof 2 is simpler (lower complexity score)"
	} else {
		comparison.SimplerProof = 0
		comparison.Recommendation = "Both proofs have similar complexity"
	}

	// Compare tactics
	tactics1 := make(map[string]bool)
	for _, t := range m1.UsedTactics {
		tactics1[t] = true
	}

	tactics2 := make(map[string]bool)
	for _, t := range m2.UsedTactics {
		tactics2[t] = true
	}

	// Find unique tactics
	for t := range tactics1 {
		if !tactics2[t] {
			comparison.UniqueTactics1 = append(comparison.UniqueTactics1, t)
		}
	}

	for t := range tactics2 {
		if !tactics1[t] {
			comparison.UniqueTactics2 = append(comparison.UniqueTactics2, t)
		}
	}

	return comparison
}

// ProofComparison contains comparison results
type ProofComparison struct {
	Proof1Metrics  *ProofMetrics
	Proof2Metrics  *ProofMetrics
	SimplerProof   int      // 1, 2, or 0 for tie
	Recommendation string   // Human-readable recommendation
	UniqueTactics1 []string // Tactics only in proof 1
	UniqueTactics2 []string // Tactics only in proof 2
}
