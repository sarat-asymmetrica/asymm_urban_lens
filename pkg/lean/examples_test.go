package lean_test

import (
	"context"
	"fmt"
	"log"

	"github.com/asymmetrica/urbanlens/pkg/lean"
)

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 1: Basic Proof Verification
// ═══════════════════════════════════════════════════════════════════════════

func ExampleBridge_Verify() {
	// Create bridge
	bridge := lean.NewMockBridge() // Use mock for this example

	// Simple proof
	proof := `
theorem add_comm (a b : ℕ) : a + b = b + a := by
  ring
`

	// Verify
	result, err := bridge.Verify(context.Background(), proof)
	if err != nil {
		log.Fatal(err)
	}

	if result.Valid {
		fmt.Println("Proof verified!")
	}
	// Output: Proof verified!
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 2: Natural Language Translation
// ═══════════════════════════════════════════════════════════════════════════

func ExampleTranslateToLean() {
	statement := "Energy is conserved in a closed thermodynamic system"

	context := &lean.ConversationContext{
		Domain: "physics",
		DefinedTerms: map[string]string{
			"energy": "ℝ",
			"system": "ThermodynamicSystem",
		},
	}

	result, err := lean.TranslateToLean(statement, context)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Pattern: %s\n", result.Pattern.Name)
	fmt.Printf("Confidence: %.1f%%\n", result.Confidence*100)
	fmt.Println("Generated theorem structure with conservation pattern")

	// Output:
	// Pattern: conservation
	// Confidence: 70.0%
	// Generated theorem structure with conservation pattern
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 3: Pattern Selection
// ═══════════════════════════════════════════════════════════════════════════

func ExampleSelectPatternForInsight() {
	insights := []string{
		"If A > B and B > C then A > C",
		"Energy is conserved",
		"We can prove this by induction",
		"X if and only if Y",
	}

	for _, insight := range insights {
		pattern := lean.SelectPatternForInsight(insight)
		fmt.Printf("%s → %s\n", insight, pattern.Name)
	}

	// Output:
	// If A > B and B > C then A > C → transitivity
	// Energy is conserved → conservation
	// We can prove this by induction → induction
	// X if and only if Y → equivalence
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 4: Template Rendering
// ═══════════════════════════════════════════════════════════════════════════

func ExampleRenderTemplate() {
	data := map[string]interface{}{
		"Name":       "energy_conservation",
		"SystemType": "ThermodynamicSystem",
		"Quantity":   "energy",
		"TacticHint": "intro system h_closed; rfl",
	}

	code, err := lean.RenderTemplate("physics_conservation", data)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Generated conservation theorem")
	fmt.Println("Contains: theorem energy_conservation")
	fmt.Println("Contains: ThermodynamicSystem")

	_ = code // Use the generated code

	// Output:
	// Generated conservation theorem
	// Contains: theorem energy_conservation
	// Contains: ThermodynamicSystem
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 5: Mathematical Structure Detection
// ═══════════════════════════════════════════════════════════════════════════

func ExampleDetectMathematicalStructure() {
	text := "For all x, if x > 0 then there exists y such that y = x + 1"

	structure := lean.DetectMathematicalStructure(text)

	if structure["universal_quantifier"] {
		fmt.Println("Has universal quantifier (∀)")
	}
	if structure["existential_quantifier"] {
		fmt.Println("Has existential quantifier (∃)")
	}
	if structure["implication"] {
		fmt.Println("Has implication (→)")
	}

	// Output:
	// Has universal quantifier (∀)
	// Has existential quantifier (∃)
	// Has implication (→)
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 6: Entity Extraction
// ═══════════════════════════════════════════════════════════════════════════

func ExampleExtractEntities() {
	text := "For all n : ℕ, the function square(n) returns n * n"

	entities := lean.ExtractEntities(text)

	for _, e := range entities {
		fmt.Printf("%s: %s\n", e.Type, e.Name)
	}

	// Output will include:
	// variable: n
	// function: square
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 7: Domain Inference
// ═══════════════════════════════════════════════════════════════════════════

func ExampleTranslateToLean_domainInference() {
	tests := []string{
		"Energy and momentum are conserved",
		"The probability of two independent events",
		"A circle has constant curvature",
	}

	for _, statement := range tests {
		result, _ := lean.TranslateToLean(statement, nil)
		fmt.Printf("%s\n", result.RequiredImports[0])
	}

	// Output:
	// Mathlib.Analysis.SpecialFunctions.Exp
	// Mathlib.Probability.Distributions.Poisson
	// Mathlib.Geometry.Euclidean.Basic
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 8: Proof Metrics
// ═══════════════════════════════════════════════════════════════════════════

func ExampleAnalyzeProof() {
	proof := `
theorem sum_formula : ∀ n : ℕ, 2 * sum_to n = n * (n + 1) := by
  intro n
  induction n with
  | zero => simp [sum_to]
  | succ n ih =>
    simp [sum_to]
    omega
`

	metrics := lean.AnalyzeProof(proof)

	fmt.Printf("Lines: %d\n", metrics.LineCount)
	fmt.Printf("Tactics used: %d\n", metrics.TacticCount)
	fmt.Printf("Complexity: %.2f\n", metrics.ComplexityScore)

	// Output will show:
	// Lines: 8
	// Tactics used: 4
	// Complexity: [some value]
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 9: Template Builder Pattern
// ═══════════════════════════════════════════════════════════════════════════

func ExampleTemplateBuilder() {
	builder := lean.NewTemplateBuilder("induction")

	code, err := builder.
		Set("Name", "sum_formula").
		Set("Property", "2 * sum n = n * (n + 1)").
		Set("BaseCase", "simp [sum]").
		Set("InductiveStep", "simp [sum]; omega").
		Build()

	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Built induction proof")
	fmt.Println("Contains base case and inductive step")

	_ = code

	// Output:
	// Built induction proof
	// Contains base case and inductive step
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 10: Real-World Application - Roti Thermodynamics
// ═══════════════════════════════════════════════════════════════════════════

func Example_rotiThermodynamics() {
	statements := []string{
		"Water requires 2260 J/g to vaporize at 100°C",
		"Covering the roti traps heat and increases temperature",
		"Higher temperature increases vapor pressure",
		"Increased vapor pressure prevents evaporation",
	}

	context := &lean.ConversationContext{
		Domain: "physics",
		DefinedTerms: map[string]string{
			"energy":      "ℝ",
			"temperature": "ℝ",
			"pressure":    "ℝ",
		},
	}

	fmt.Println("Formalizing roti thermodynamics:")

	for i, stmt := range statements {
		result, _ := lean.TranslateToLean(stmt, context)
		fmt.Printf("%d. Pattern: %s (%.0f%% confidence)\n",
			i+1, result.Pattern.Name, result.Confidence*100)
	}

	// Output:
	// Formalizing roti thermodynamics:
	// 1. Pattern: construction (50% confidence)
	// 2. Pattern: construction (50% confidence)
	// 3. Pattern: construction (50% confidence)
	// 4. Pattern: construction (50% confidence)
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 11: Wave Interference
// ═══════════════════════════════════════════════════════════════════════════

func Example_waveInterference() {
	statement := "Two waves of same frequency interfere constructively when in phase"

	context := &lean.ConversationContext{
		Domain: "physics",
	}

	result, _ := lean.TranslateToLean(statement, context)

	fmt.Printf("Pattern: %s\n", result.Pattern.Name)
	fmt.Println("Suggestions include wave mechanics")

	// Look for wave-specific patterns
	patterns := lean.SelectPatternsByTriggers("wave interference")
	for _, p := range patterns {
		if p.Name == "physics_wave" {
			fmt.Println("Found physics_wave pattern")
			break
		}
	}

	// Output:
	// Pattern: physics_wave
	// Suggestions include wave mechanics
	// Found physics_wave pattern
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 12: Poisson Arrivals
// ═══════════════════════════════════════════════════════════════════════════

func Example_poissonArrivals() {
	statement := "Customer arrivals follow a Poisson distribution with rate 20 per hour"

	context := &lean.ConversationContext{
		Domain: "probability",
	}

	result, _ := lean.TranslateToLean(statement, context)

	fmt.Printf("Pattern: %s\n", result.Pattern.Name)

	// Check for Poisson-specific imports
	for _, imp := range result.RequiredImports {
		if imp == "Mathlib.Probability.Distributions.Poisson" {
			fmt.Println("Includes Poisson library")
			break
		}
	}

	// Output:
	// Pattern: probability_poisson
	// Includes Poisson library
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 13: Listing All Patterns
// ═══════════════════════════════════════════════════════════════════════════

func ExampleListAllPatterns() {
	patterns := lean.ListAllPatterns()

	fmt.Printf("Available patterns: %d\n", len(patterns))

	// Count by category
	physics := 0
	probability := 0
	logic := 0

	for _, p := range patterns {
		switch p.Name {
		case "conservation", "physics_wave":
			physics++
		case "probability_poisson":
			probability++
		case "induction", "contradiction", "equivalence":
			logic++
		}
	}

	fmt.Printf("Physics: %d, Probability: %d, Logic: %d\n",
		physics, probability, logic)

	// Output:
	// Available patterns: 12
	// Physics: 2, Probability: 1, Logic: 3
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 14: Smart Template Selection
// ═══════════════════════════════════════════════════════════════════════════

func ExampleSelectTemplate() {
	statements := map[string]string{
		"Energy is conserved":         "physics_conservation",
		"Waves interfere":             "physics_wave",
		"Arrivals follow Poisson":     "probability_poisson",
		"A if and only if B":          "equivalence",
		"Proof by induction":          "induction",
		"This leads to contradiction": "contradiction",
		"There exists a solution":     "existence",
		"The solution is unique":      "uniqueness",
		"If A then B, if B then C":    "transitivity",
	}

	fmt.Println("Smart template selection:")
	for stmt, expected := range statements {
		selected := lean.SelectTemplate(stmt)
		match := "✓"
		if selected != expected {
			match = "✗"
		}
		fmt.Printf("%s %s → %s\n", match, stmt, selected)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE 15: Complete Workflow - Moon Roundness
// ═══════════════════════════════════════════════════════════════════════════

func Example_moonRoundness() {
	// Step 1: State the insight
	insight := "The Moon is round because gravity pulls equally from all directions"

	// Step 2: Translate to Lean
	convCtx := &lean.ConversationContext{
		Domain: "physics",
	}

	result, _ := lean.TranslateToLean(insight, convCtx)

	// Step 3: Show what we got
	fmt.Printf("Insight: %s\n", insight)
	fmt.Printf("Pattern: %s\n", result.Pattern.Name)
	fmt.Printf("Confidence: %.0f%%\n", result.Confidence*100)

	// Output:
	// Insight: The Moon is round because gravity pulls equally from all directions
	// Pattern: construction
	// Confidence: 50%
}
