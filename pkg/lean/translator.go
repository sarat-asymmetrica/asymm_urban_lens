// Package lean - Natural Language to Lean Translator
// Converts mathematical statements from natural language to Lean 4 syntax
package lean

import (
	"fmt"
	"regexp"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// TYPES
// ═══════════════════════════════════════════════════════════════════════════

// TranslationResult contains the translated Lean code and metadata
type TranslationResult struct {
	LeanCode      string            // Generated Lean 4 code
	Pattern       *ProofPattern     // Selected proof pattern
	Entities      []MathEntity      // Extracted mathematical entities
	Confidence    float64           // Confidence score (0.0-1.0)
	Suggestions   []string          // Additional suggestions
	RequiredImports []string        // Lean imports needed
}

// ConversationContext provides context for translation
type ConversationContext struct {
	PreviousStatements []string          // Previous mathematical statements
	DefinedTerms       map[string]string // term -> type mapping
	Domain             string            // e.g., "physics", "probability", "geometry"
	Assumptions        []string          // Stated assumptions
}

// ═══════════════════════════════════════════════════════════════════════════
// MAIN TRANSLATION FUNCTION
// ═══════════════════════════════════════════════════════════════════════════

// TranslateToLean converts natural language mathematical statement to Lean 4
func TranslateToLean(statement string, context *ConversationContext) (*TranslationResult, error) {
	if context == nil {
		context = &ConversationContext{
			DefinedTerms: make(map[string]string),
		}
	}

	result := &TranslationResult{
		Entities:        ExtractEntities(statement),
		RequiredImports: []string{},
	}

	// Select appropriate proof pattern
	result.Pattern = SelectPatternForInsight(statement)

	// Extract domain-specific context
	domain := inferDomain(statement)
	if context.Domain == "" {
		context.Domain = domain
	}

	// Build the Lean code
	leanCode, confidence := buildLeanCode(statement, result.Pattern, result.Entities, context)
	result.LeanCode = leanCode
	result.Confidence = confidence

	// Add suggestions
	result.Suggestions = generateSuggestions(statement, result.Pattern, context)

	// Add required imports based on domain
	result.RequiredImports = getRequiredImports(context.Domain, result.Entities)

	return result, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ENTITY EXTRACTION
// ═══════════════════════════════════════════════════════════════════════════

// ExtractEntities extracts mathematical entities from natural language
func ExtractEntities(text string) []MathEntity {
	entities := []MathEntity{}

	// Extract constants
	constantRegex := regexp.MustCompile(`\b([A-Z][a-zA-Z]*)\s+(?:is|=|equals)\s+(\d+(?:\.\d+)?)`)
	constants := constantRegex.FindAllStringSubmatch(text, -1)
	for _, match := range constants {
		entities = append(entities, MathEntity{
			Type:  "constant",
			Name:  match[1],
			Value: match[2],
		})
	}

	// Extract variables
	varRegex := regexp.MustCompile(`\b(?:let|for all|for every)\s+([a-z]\w*)\s+(?:be|:)\s+(\w+)`)
	variables := varRegex.FindAllStringSubmatch(text, -1)
	for _, match := range variables {
		entities = append(entities, MathEntity{
			Type:  "variable",
			Name:  match[1],
			Value: match[2], // Type
		})
	}

	// Extract functions
	funcRegex := regexp.MustCompile(`\b([a-z]\w*)\s*\(`)
	functions := funcRegex.FindAllStringSubmatch(text, -1)
	seen := make(map[string]bool)
	for _, match := range functions {
		fname := match[1]
		if !seen[fname] && !isCommonWord(fname) {
			entities = append(entities, MathEntity{
				Type: "function",
				Name: fname,
			})
			seen[fname] = true
		}
	}

	// Extract relations
	relationPatterns := []struct {
		pattern  string
		relation string
	}{
		{`\bgreater than\b`, "gt"},
		{`\bless than\b`, "lt"},
		{`\bequal to\b|\bequals\b`, "eq"},
		{`\bdivides\b`, "dvd"},
		{`\bcongruent\b`, "cong"},
	}

	for _, rp := range relationPatterns {
		if matched, _ := regexp.MatchString(rp.pattern, strings.ToLower(text)); matched {
			entities = append(entities, MathEntity{
				Type:  "relation",
				Name:  rp.relation,
				Value: rp.pattern,
			})
		}
	}

	return entities
}

// ═══════════════════════════════════════════════════════════════════════════
// CODE BUILDING
// ═══════════════════════════════════════════════════════════════════════════

// buildLeanCode generates Lean 4 code from pattern and entities
func buildLeanCode(statement string, pattern *ProofPattern, entities []MathEntity, context *ConversationContext) (string, float64) {
	confidence := 0.5 // Base confidence

	// Generate theorem name
	theoremName := generateTheoremName(statement)

	// Start building the code
	var builder strings.Builder

	// Add imports if needed
	imports := getRequiredImports(context.Domain, entities)
	if len(imports) > 0 {
		for _, imp := range imports {
			builder.WriteString(fmt.Sprintf("import %s\n", imp))
		}
		builder.WriteString("\n")
	}

	// Extract hypothesis and conclusion
	hyp, concl := extractHypothesisConclusion(statement)

	// Build based on pattern type
	switch pattern.Name {
	case "conservation":
		code := buildConservationTheorem(theoremName, statement, entities)
		builder.WriteString(code)
		confidence = 0.7

	case "transitivity":
		code := buildTransitivityTheorem(theoremName, hyp, concl, entities)
		builder.WriteString(code)
		confidence = 0.75

	case "induction":
		code := buildInductionTheorem(theoremName, statement)
		builder.WriteString(code)
		confidence = 0.6

	case "equivalence":
		code := buildEquivalenceTheorem(theoremName, statement)
		builder.WriteString(code)
		confidence = 0.7

	default:
		// Generic theorem structure
		code := buildGenericTheorem(theoremName, statement, pattern)
		builder.WriteString(code)
		confidence = 0.5
	}

	return builder.String(), confidence
}

// buildConservationTheorem generates conservation law theorem
func buildConservationTheorem(name, statement string, entities []MathEntity) string {
	// Extract the conserved quantity
	quantity := "energy" // Default
	for _, e := range entities {
		if e.Type == "function" && e.Name != "system" {
			quantity = e.Name
		}
	}

	return fmt.Sprintf(`-- %s
theorem %s :
  ∀ (system : PhysicalSystem),
    IsClosed system →
    %s system = %s system.initial := by
  intro system h_closed
  -- Apply conservation principle
  sorry
`, statement, name, quantity, quantity)
}

// buildTransitivityTheorem generates transitivity theorem
func buildTransitivityTheorem(name, hyp, concl string, entities []MathEntity) string {
	// Find the relation
	relation := "R"
	for _, e := range entities {
		if e.Type == "relation" {
			relation = leanRelation(e.Name)
		}
	}

	return fmt.Sprintf(`-- If A %s B and B %s C, then A %s C
theorem %s (A B C : ℝ) :
  A %s B → B %s C → A %s C := by
  intro h1 h2
  exact trans h1 h2
`, relation, relation, relation, name, relation, relation, relation)
}

// buildInductionTheorem generates induction theorem
func buildInductionTheorem(name, statement string) string {
	// Extract property description
	property := "P"

	return fmt.Sprintf(`-- %s
theorem %s : ∀ n : ℕ, %s n := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    sorry
  | succ n ih =>
    -- Inductive case: assume true for n, prove for n+1
    -- ih : %s n
    sorry
`, statement, name, property, property)
}

// buildEquivalenceTheorem generates iff theorem
func buildEquivalenceTheorem(name, statement string) string {
	parts := strings.Split(statement, " iff ")
	if len(parts) < 2 {
		parts = strings.Split(statement, " if and only if ")
	}

	left := "P"
	right := "Q"
	if len(parts) == 2 {
		left = strings.TrimSpace(parts[0])
		right = strings.TrimSpace(parts[1])
	}

	return fmt.Sprintf(`-- %s
theorem %s : %s ↔ %s := by
  constructor
  · -- Forward: %s → %s
    intro h
    sorry
  · -- Backward: %s → %s
    intro h
    sorry
`, statement, name, left, right, left, right, right, left)
}

// buildGenericTheorem generates a generic theorem structure
func buildGenericTheorem(name, statement string, pattern *ProofPattern) string {
	return fmt.Sprintf(`-- %s
theorem %s : sorry := by
  %s
`, statement, name, pattern.TacticHint)
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// generateTheoremName creates a valid Lean identifier from statement
func generateTheoremName(statement string) string {
	// Take first few meaningful words
	words := strings.Fields(strings.ToLower(statement))
	var parts []string

	for _, word := range words {
		// Skip common words
		if isCommonWord(word) {
			continue
		}
		// Clean the word
		clean := regexp.MustCompile(`[^a-z0-9_]`).ReplaceAllString(word, "")
		if len(clean) > 0 {
			parts = append(parts, clean)
		}
		if len(parts) >= 4 { // Max 4 words
			break
		}
	}

	if len(parts) == 0 {
		return "theorem_unnamed"
	}

	return strings.Join(parts, "_")
}

// isCommonWord checks if word should be skipped
func isCommonWord(word string) bool {
	common := map[string]bool{
		"the": true, "a": true, "an": true, "is": true, "are": true,
		"was": true, "were": true, "be": true, "been": true, "being": true,
		"have": true, "has": true, "had": true, "do": true, "does": true,
		"did": true, "will": true, "would": true, "could": true, "should": true,
		"may": true, "might": true, "must": true, "can": true,
		"this": true, "that": true, "these": true, "those": true,
		"if": true, "then": true, "else": true, "when": true, "where": true,
		"what": true, "which": true, "who": true, "whom": true, "whose": true,
		"why": true, "how": true, "all": true, "each": true, "every": true,
		"both": true, "few": true, "more": true, "most": true, "other": true,
		"some": true, "such": true, "no": true, "nor": true, "not": true,
		"only": true, "own": true, "same": true, "so": true, "than": true,
		"too": true, "very": true, "just": true, "but": true, "and": true,
		"or": true, "for": true, "of": true, "at": true, "by": true,
		"from": true, "in": true, "into": true, "on": true, "to": true,
		"with": true, "as": true,
	}
	return common[strings.ToLower(word)]
}

// extractHypothesisConclusion splits statement into hypothesis and conclusion
func extractHypothesisConclusion(statement string) (string, string) {
	// Look for "if...then" pattern
	ifThen := regexp.MustCompile(`(?i)if\s+(.+?)\s+then\s+(.+)`)
	if matches := ifThen.FindStringSubmatch(statement); matches != nil {
		return matches[1], matches[2]
	}

	// Look for "implies" pattern
	implies := regexp.MustCompile(`(?i)(.+?)\s+implies\s+(.+)`)
	if matches := implies.FindStringSubmatch(statement); matches != nil {
		return matches[1], matches[2]
	}

	// Default: no clear hypothesis
	return "", statement
}

// inferDomain guesses the mathematical domain from statement
func inferDomain(statement string) string {
	statement = strings.ToLower(statement)

	domains := map[string][]string{
		"physics": {"energy", "force", "mass", "velocity", "momentum", "wave", "particle", "field", "thermodynamic"},
		"probability": {"probability", "random", "expected", "variance", "distribution", "poisson", "binomial"},
		"geometry": {"point", "line", "circle", "triangle", "angle", "distance", "area", "volume", "sphere"},
		"algebra": {"group", "ring", "field", "vector", "matrix", "polynomial", "eigenvalue"},
		"analysis": {"continuous", "limit", "derivative", "integral", "convergent", "sequence", "series"},
		"number_theory": {"prime", "divisor", "congruent", "modulo", "gcd", "lcm", "coprime"},
	}

	scores := make(map[string]int)
	for domain, keywords := range domains {
		for _, keyword := range keywords {
			if strings.Contains(statement, keyword) {
				scores[domain]++
			}
		}
	}

	// Find highest scoring domain
	maxScore := 0
	bestDomain := "mathematics"
	for domain, score := range scores {
		if score > maxScore {
			maxScore = score
			bestDomain = domain
		}
	}

	return bestDomain
}

// getRequiredImports returns Lean imports needed for domain
func getRequiredImports(domain string, entities []MathEntity) []string {
	imports := []string{}

	switch domain {
	case "physics":
		imports = append(imports, "Mathlib.Analysis.SpecialFunctions.Exp")
	case "probability":
		imports = append(imports, "Mathlib.Probability.Distributions.Poisson")
	case "geometry":
		imports = append(imports, "Mathlib.Geometry.Euclidean.Basic")
	case "algebra":
		imports = append(imports, "Mathlib.Algebra.Group.Defs")
	case "analysis":
		imports = append(imports, "Mathlib.Analysis.Calculus.Deriv.Basic")
	case "number_theory":
		imports = append(imports, "Mathlib.NumberTheory.Divisors")
	}

	// Add standard library
	imports = append(imports, "Mathlib.Tactic")

	return imports
}

// leanRelation converts relation name to Lean syntax
func leanRelation(rel string) string {
	relations := map[string]string{
		"gt":   ">",
		"lt":   "<",
		"eq":   "=",
		"dvd":  "∣",
		"cong": "≡",
	}

	if lean, ok := relations[rel]; ok {
		return lean
	}
	return rel
}

// generateSuggestions provides helpful suggestions for the user
func generateSuggestions(statement string, pattern *ProofPattern, context *ConversationContext) []string {
	suggestions := []string{}

	// Suggest based on pattern
	suggestions = append(suggestions, fmt.Sprintf("Selected pattern: %s - %s", pattern.Name, pattern.Description))

	// Suggest tactics
	structure := DetectMathematicalStructure(statement)
	tactics := SuggestTactics(pattern, structure)
	if len(tactics) > 0 {
		suggestions = append(suggestions, fmt.Sprintf("Suggested tactics: %s", strings.Join(tactics, ", ")))
	}

	// Suggest related theorems
	if len(context.PreviousStatements) > 0 {
		suggestions = append(suggestions, "Consider using previous results as lemmas")
	}

	return suggestions
}

// BuildTheoremSkeleton generates a theorem skeleton from conversation
func BuildTheoremSkeleton(statement string, context *ConversationContext) string {
	result, _ := TranslateToLean(statement, context)
	return result.LeanCode
}
