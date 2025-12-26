// Package lean - Proof Pattern Library
// Common mathematical proof patterns for automatic generation
package lean

import (
	"regexp"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// TYPES
// ═══════════════════════════════════════════════════════════════════════════

// ProofPattern represents a reusable proof structure
type ProofPattern struct {
	Name        string   // Pattern identifier (e.g., "conservation", "transitivity")
	Description string   // Human-readable description
	Template    string   // Lean code template with {{placeholders}}
	Triggers    []string // Natural language phrases that suggest this pattern
	Example     string   // Concrete example usage
	TacticHint  string   // Suggested Lean tactics
}

// MathEntity represents a mathematical object extracted from natural language
type MathEntity struct {
	Type  string // "constant", "variable", "function", "relation", "set"
	Name  string // The identifier
	Value string // Optional value or definition
}

// ═══════════════════════════════════════════════════════════════════════════
// PATTERN LIBRARY
// ═══════════════════════════════════════════════════════════════════════════

// ProofPatterns is the global library of common proof patterns
var ProofPatterns = map[string]ProofPattern{
	"conservation": {
		Name:        "conservation",
		Description: "Conservation law - a quantity remains constant over time",
		Template: `theorem {{.Name}} :
  ∀ (system : {{.SystemType}}),
    IsClosed system →
    {{.Quantity}} system = {{.Quantity}} system.initial := by
  {{.TacticHint}}`,
		Triggers: []string{
			"conserved",
			"remains constant",
			"doesn't change",
			"invariant",
			"preserved",
			"stays the same",
		},
		Example: `theorem energy_conservation :
  ∀ (system : ThermodynamicSystem),
    IsClosed system →
    energy system = energy system.initial := by
  sorry`,
		TacticHint: "intro system; intro h_closed; exact conservation_law system h_closed",
	},

	"transitivity": {
		Name:        "transitivity",
		Description: "If A relates to B and B relates to C, then A relates to C",
		Template: `theorem {{.Name}} ({{.Vars}}) :
  {{.A}} {{.Relation}} {{.B}} →
  {{.B}} {{.Relation}} {{.C}} →
  {{.A}} {{.Relation}} {{.C}} := by
  {{.TacticHint}}`,
		Triggers: []string{
			"if.*and.*then",
			"follows from",
			"chains together",
			"transitively",
		},
		Example: `theorem temperature_transitivity (A B C : Object) :
  temp A > temp B →
  temp B > temp C →
  temp A > temp C := by
  intro h1 h2; exact Nat.lt_trans h2 h1`,
		TacticHint: "intro h1 h2; exact trans h1 h2",
	},

	"induction": {
		Name:        "induction",
		Description: "Mathematical induction - prove base case and inductive step",
		Template: `theorem {{.Name}} : ∀ n : ℕ, {{.Property}} n := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    {{.BaseCase}}
  | succ n ih =>
    -- Inductive case: assume true for n, prove for n+1
    {{.InductiveStep}}`,
		Triggers: []string{
			"for all natural numbers",
			"for every n",
			"by induction",
			"base case",
			"inductive step",
		},
		Example: `theorem sum_formula : ∀ n : ℕ, 2 * sum_to n = n * (n + 1) := by
  intro n
  induction n with
  | zero => simp [sum_to]
  | succ n ih =>
    simp [sum_to]
    omega`,
		TacticHint: "intro n; induction n with | zero => sorry | succ n ih => sorry",
	},

	"contradiction": {
		Name:        "contradiction",
		Description: "Proof by contradiction - assume negation leads to absurdity",
		Template: `theorem {{.Name}} : {{.Claim}} := by
  by_contra h_neg
  -- Assume ¬{{.Claim}}
  {{.DeriveFalse}}
  -- This leads to contradiction`,
		Triggers: []string{
			"impossible",
			"cannot be",
			"leads to contradiction",
			"assume the opposite",
		},
		Example: `theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  by_contra h
  -- Assuming √2 is rational leads to contradiction
  sorry`,
		TacticHint: "by_contra h; sorry",
	},

	"construction": {
		Name:        "construction",
		Description: "Constructive proof - explicitly build the object",
		Template: `theorem {{.Name}} : ∃ x : {{.Type}}, {{.Property}} x := by
  use {{.Witness}}
  -- Show that witness satisfies property
  {{.Verification}}`,
		Triggers: []string{
			"there exists",
			"we can construct",
			"take",
			"choose",
			"witness",
		},
		Example: `theorem exists_even : ∃ n : ℕ, Even n := by
  use 2
  exact ⟨1, rfl⟩`,
		TacticHint: "use witness; sorry",
	},

	"equivalence": {
		Name:        "equivalence",
		Description: "Prove A ↔ B by showing A → B and B → A",
		Template: `theorem {{.Name}} : {{.A}} ↔ {{.B}} := by
  constructor
  · -- Forward direction: A → B
    intro h
    {{.ForwardProof}}
  · -- Backward direction: B → A
    intro h
    {{.BackwardProof}}`,
		Triggers: []string{
			"if and only if",
			"equivalent",
			"iff",
			"necessary and sufficient",
		},
		Example: `theorem even_iff_div_two (n : ℕ) : Even n ↔ 2 ∣ n := by
  constructor
  · intro ⟨k, hk⟩; use k; exact hk
  · intro ⟨k, hk⟩; use k; exact hk`,
		TacticHint: "constructor; · sorry; · sorry",
	},

	"cases": {
		Name:        "cases",
		Description: "Proof by case analysis",
		Template: `theorem {{.Name}} : {{.Claim}} := by
  cases {{.Subject}} with
  {{.CaseAnalysis}}`,
		Triggers: []string{
			"in each case",
			"consider cases",
			"either.*or",
			"case by case",
		},
		Example: `theorem abs_nonneg (x : ℤ) : 0 ≤ |x| := by
  cases x.sign with
  | neg => simp [abs]; omega
  | zero => simp
  | pos => simp [abs]`,
		TacticHint: "cases subject with | case1 => sorry | case2 => sorry",
	},

	"uniqueness": {
		Name:        "uniqueness",
		Description: "Prove that a property determines an object uniquely",
		Template: `theorem {{.Name}} :
  ∀ x y : {{.Type}},
    {{.Property}} x →
    {{.Property}} y →
    x = y := by
  intro x y hx hy
  {{.ShowEqual}}`,
		Triggers: []string{
			"unique",
			"only one",
			"at most one",
			"determined uniquely",
		},
		Example: `theorem identity_unique (f : ℕ → ℕ) :
  (∀ x, f x = x) →
  (∀ x, id x = x) →
  f = id := by
  intro hf hid
  ext x
  rw [hf, hid]`,
		TacticHint: "intro x y hx hy; sorry",
	},

	"pigeonhole": {
		Name:        "pigeonhole",
		Description: "If more objects than containers, at least one container has multiple objects",
		Template: `theorem {{.Name}} :
  ∀ (objects : Finset α) (containers : Finset β) (assign : α → β),
    objects.card > containers.card →
    ∃ b : β, (objects.filter (λ a => assign a = b)).card ≥ 2 := by
  {{.TacticHint}}`,
		Triggers: []string{
			"pigeonhole",
			"more.*than",
			"at least two",
			"collision",
		},
		Example: `-- Classic pigeonhole principle
theorem pigeonhole_basic (n : ℕ) :
  ∀ f : Fin (n + 2) → Fin (n + 1),
    ∃ i j, i ≠ j ∧ f i = f j := by
  sorry`,
		TacticHint: "intro objects containers assign h_card; sorry",
	},

	"continuity": {
		Name:        "continuity",
		Description: "A function is continuous if it preserves limits",
		Template: `theorem {{.Name}} : Continuous {{.Function}} := by
  rw [continuous_def]
  intro x
  {{.EpsilonDelta}}`,
		Triggers: []string{
			"continuous",
			"no jumps",
			"smooth",
			"preserves limits",
		},
		Example: `theorem continuous_add : Continuous (λ x : ℝ × ℝ => x.1 + x.2) := by
  continuity`,
		TacticHint: "rw [continuous_def]; intro x; sorry",
	},

	"physics_wave": {
		Name:        "physics_wave",
		Description: "Wave interference and superposition",
		Template: `theorem {{.Name}} :
  ∀ (w1 w2 : Wave),
    amplitude (w1 + w2) =
      amplitude w1 + amplitude w2 +
      2 * Real.sqrt (intensity w1 * intensity w2) * Real.cos (phase_diff w1 w2) := by
  {{.TacticHint}}`,
		Triggers: []string{
			"wave",
			"interference",
			"superposition",
			"constructive",
			"destructive",
		},
		Example: `-- Wave superposition principle
theorem wave_superposition (w1 w2 : Wave) :
  intensity (w1 + w2) ≤
  intensity w1 + intensity w2 +
  2 * Real.sqrt (intensity w1 * intensity w2) := by
  sorry`,
		TacticHint: "intro w1 w2; simp [amplitude, intensity]; sorry",
	},

	"probability_poisson": {
		Name:        "probability_poisson",
		Description: "Poisson distribution for rare events",
		Template: `theorem {{.Name}} (λ : ℝ) (h_pos : 0 < λ) :
  ∑' k, poisson_pmf λ k = 1 := by
  rw [poisson_pmf]
  {{.TacticHint}}`,
		Triggers: []string{
			"poisson",
			"rare events",
			"arrival rate",
			"exponential",
		},
		Example: `-- Poisson distribution sums to 1
theorem poisson_total_prob (λ : ℝ) (h : 0 < λ) :
  ∑' k, (λ^k * Real.exp (-λ)) / Nat.factorial k = 1 := by
  sorry`,
		TacticHint: "rw [poisson_pmf]; sorry",
	},
}

// ═══════════════════════════════════════════════════════════════════════════
// PATTERN SELECTION
// ═══════════════════════════════════════════════════════════════════════════

// SelectPatternForInsight analyzes natural language and suggests appropriate proof pattern
func SelectPatternForInsight(insight string) *ProofPattern {
	insight = strings.ToLower(insight)

	// Score each pattern by trigger matches
	bestScore := 0
	var bestPattern *ProofPattern

	for _, pattern := range ProofPatterns {
		score := 0
		for _, trigger := range pattern.Triggers {
			// Use regex for more flexible matching
			matched, _ := regexp.MatchString(trigger, insight)
			if matched {
				score++
			}
		}

		if score > bestScore {
			bestScore = score
			p := pattern // Copy to avoid pointer issues
			bestPattern = &p
		}
	}

	// Default to construction if no clear match
	if bestPattern == nil {
		p := ProofPatterns["construction"]
		bestPattern = &p
	}

	return bestPattern
}

// SelectPatternsByTriggers finds all patterns matching any trigger
func SelectPatternsByTriggers(text string) []ProofPattern {
	text = strings.ToLower(text)

	var matched []ProofPattern
	seen := make(map[string]bool)

	for name, pattern := range ProofPatterns {
		if seen[name] {
			continue
		}

		for _, trigger := range pattern.Triggers {
			if match, _ := regexp.MatchString(trigger, text); match {
				matched = append(matched, pattern)
				seen[name] = true
				break
			}
		}
	}

	return matched
}

// GetPatternByName retrieves a specific pattern by name
func GetPatternByName(name string) (*ProofPattern, bool) {
	pattern, exists := ProofPatterns[name]
	return &pattern, exists
}

// ListAllPatterns returns all available patterns
func ListAllPatterns() []ProofPattern {
	patterns := make([]ProofPattern, 0, len(ProofPatterns))
	for _, p := range ProofPatterns {
		patterns = append(patterns, p)
	}
	return patterns
}

// ═══════════════════════════════════════════════════════════════════════════
// PATTERN MATCHING HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// DetectMathematicalStructure identifies structural features in the text
func DetectMathematicalStructure(text string) map[string]bool {
	text = strings.ToLower(text)

	features := make(map[string]bool)

	// Quantifiers
	if regexp.MustCompile(`\bfor all\b|\bevery\b|∀`).MatchString(text) {
		features["universal_quantifier"] = true
	}
	if regexp.MustCompile(`\bthere exists\b|\bsome\b|∃`).MatchString(text) {
		features["existential_quantifier"] = true
	}

	// Logical connectives
	if regexp.MustCompile(`\bif and only if\b|\biff\b|↔`).MatchString(text) {
		features["biconditional"] = true
	}
	if regexp.MustCompile(`\bimplies\b|\bif.*then\b|→`).MatchString(text) {
		features["implication"] = true
	}

	// Mathematical operations
	if regexp.MustCompile(`\bsum\b|\btotal\b|∑`).MatchString(text) {
		features["summation"] = true
	}
	if regexp.MustCompile(`\bproduct\b|∏`).MatchString(text) {
		features["product"] = true
	}

	// Relations
	if regexp.MustCompile(`\bequal\b|\bsame\b|=`).MatchString(text) {
		features["equality"] = true
	}
	if regexp.MustCompile(`\bless than\b|\bgreater than\b|<|>`).MatchString(text) {
		features["inequality"] = true
	}

	// Proof techniques
	if regexp.MustCompile(`\binduction\b`).MatchString(text) {
		features["induction"] = true
	}
	if regexp.MustCompile(`\bcontradiction\b|\bimpossible\b`).MatchString(text) {
		features["contradiction"] = true
	}

	return features
}

// SuggestTactics suggests Lean tactics based on pattern and context
func SuggestTactics(pattern *ProofPattern, context map[string]bool) []string {
	tactics := []string{}

	// Start with pattern's own hint
	if pattern.TacticHint != "" {
		tactics = append(tactics, pattern.TacticHint)
	}

	// Add context-based suggestions
	if context["universal_quantifier"] {
		tactics = append(tactics, "intro")
	}
	if context["existential_quantifier"] {
		tactics = append(tactics, "use <witness>")
	}
	if context["biconditional"] {
		tactics = append(tactics, "constructor")
	}
	if context["induction"] {
		tactics = append(tactics, "induction n with | zero => sorry | succ n ih => sorry")
	}
	if context["contradiction"] {
		tactics = append(tactics, "by_contra h")
	}
	if context["equality"] {
		tactics = append(tactics, "rfl", "simp", "ring")
	}

	return tactics
}
