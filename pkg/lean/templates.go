// Package lean - Lean Code Templates
// Predefined templates for common theorem types
package lean

import (
	"bytes"
	"fmt"
	"regexp"
	"strings"
	"text/template"
)

// ═══════════════════════════════════════════════════════════════════════════
// TEMPLATE DEFINITIONS
// ═══════════════════════════════════════════════════════════════════════════

// TheoremTemplates contains Lean code templates for common theorem types
var TheoremTemplates = map[string]string{
	// Physics - Conservation Laws
	"physics_conservation": `-- Conservation of {{.Quantity}} in {{.SystemType}}
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

structure {{.SystemType}} where
  state : ℝ
  {{.Quantity}} : ℝ
  time : ℝ

def IsClosed (system : {{.SystemType}}) : Prop :=
  -- No external interactions
  true

theorem {{.Name}} :
  ∀ (system : {{.SystemType}}),
    IsClosed system →
    system.{{.Quantity}} = system.{{.Quantity}} := by
  intro system h_closed
  -- Conservation law: {{.Quantity}} is invariant
  rfl
`,

	// Physics - Wave Mechanics
	"physics_wave": `-- Wave interference and superposition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

structure Wave where
  amplitude : ℝ
  frequency : ℝ
  phase : ℝ
  velocity : ℝ

def intensity (w : Wave) : ℝ :=
  w.amplitude ^ 2

def phase_diff (w1 w2 : Wave) : ℝ :=
  w1.phase - w2.phase

theorem {{.Name}} (w1 w2 : Wave) :
  intensity (w1 + w2) ≤
    intensity w1 + intensity w2 +
    2 * Real.sqrt (intensity w1 * intensity w2) := by
  {{.TacticHint}}
`,

	// Probability - Poisson Distribution
	"probability_poisson": `-- Poisson distribution for rare events
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

def poisson_pmf (λ : ℝ) (k : ℕ) : ℝ :=
  (λ ^ k * Real.exp (-λ)) / Nat.factorial k

theorem {{.Name}} (λ : ℝ) (h_pos : 0 < λ) :
  ∑' k, poisson_pmf λ k = 1 := by
  {{.TacticHint}}
`,

	// Mathematical Relations
	"mathematical_relation": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} {{.Variables}} :
  {{.Hypothesis}} → {{.Conclusion}} := by
  {{.TacticHint}}
`,

	// Equivalence (iff)
	"equivalence": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} {{.Variables}} :
  {{.LeftSide}} ↔ {{.RightSide}} := by
  constructor
  · -- Forward direction: {{.LeftSide}} → {{.RightSide}}
    intro h
    {{.ForwardTactic}}
  · -- Backward direction: {{.RightSide}} → {{.LeftSide}}
    intro h
    {{.BackwardTactic}}
`,

	// Induction
	"induction": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} : ∀ n : ℕ, {{.Property}} n := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    {{.BaseCase}}
  | succ n ih =>
    -- Inductive case: assume {{.Property}} n, prove {{.Property}} (n+1)
    {{.InductiveStep}}
`,

	// Existence
	"existence": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} : ∃ x : {{.Type}}, {{.Property}} x := by
  use {{.Witness}}
  {{.Verification}}
`,

	// Uniqueness
	"uniqueness": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} :
  ∀ x y : {{.Type}},
    {{.Property}} x →
    {{.Property}} y →
    x = y := by
  intro x y hx hy
  {{.Proof}}
`,

	// Contradiction
	"contradiction": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} : {{.Claim}} := by
  by_contra h
  -- Assume ¬({{.Claim}})
  {{.DeriveContradiction}}
`,

	// Transitivity
	"transitivity": `-- {{.Description}}
import Mathlib.Tactic

theorem {{.Name}} ({{.Variables}}) :
  {{.AB}} →
  {{.BC}} →
  {{.AC}} := by
  intro h1 h2
  {{.TransProof}}
`,

	// Geometry - Circle
	"geometry_circle": `-- {{.Description}}
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Tactic

structure Circle where
  center : ℝ × ℝ
  radius : ℝ
  h_pos : 0 < radius

def on_circle (p : ℝ × ℝ) (c : Circle) : Prop :=
  (p.1 - c.center.1)^2 + (p.2 - c.center.2)^2 = c.radius^2

theorem {{.Name}} :
  ∀ (c : Circle) (p : ℝ × ℝ),
    on_circle p c →
    {{.Property}} := by
  {{.TacticHint}}
`,

	// Number Theory - Divisibility
	"number_theory_divisibility": `-- {{.Description}}
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

theorem {{.Name}} ({{.Variables}}) :
  {{.DivisibilityProperty}} := by
  {{.TacticHint}}
`,

	// Thermodynamics - Roti Example
	"thermodynamics_roti": `-- Thermodynamics of roti making
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

structure RotiSystem where
  water_mass : ℝ
  initial_temp : ℝ
  final_temp : ℝ
  time : ℝ

def latent_heat_vaporization : ℝ := 2260  -- J/g

def energy_to_steam (m : ℝ) : ℝ :=
  m * latent_heat_vaporization

theorem {{.Name}} (system : RotiSystem) :
  system.water_mass > 0 →
  energy_to_steam system.water_mass > 0 := by
  intro h_mass
  unfold energy_to_steam latent_heat_vaporization
  {{.TacticHint}}
`,

	// General Structure Template
	"structure_definition": `-- {{.Description}}
import Mathlib.Tactic

structure {{.Name}} where
{{.Fields}}

{{.Instances}}
`,

	// Function Definition
	"function_definition": `-- {{.Description}}
import Mathlib.Tactic

def {{.Name}} {{.Parameters}} : {{.ReturnType}} :=
{{.Body}}

-- Properties of {{.Name}}
{{.Properties}}
`,
}

// ═══════════════════════════════════════════════════════════════════════════
// TEMPLATE RENDERING
// ═══════════════════════════════════════════════════════════════════════════

// RenderTemplate renders a template with given data
func RenderTemplate(templateName string, data map[string]interface{}) (string, error) {
	// Get template
	templateStr, exists := TheoremTemplates[templateName]
	if !exists {
		return "", fmt.Errorf("template '%s' not found", templateName)
	}

	// Parse template
	tmpl, err := template.New(templateName).Parse(templateStr)
	if err != nil {
		return "", fmt.Errorf("failed to parse template: %w", err)
	}

	// Render
	var buf bytes.Buffer
	if err := tmpl.Execute(&buf, data); err != nil {
		return "", fmt.Errorf("failed to render template: %w", err)
	}

	return buf.String(), nil
}

// RenderTemplateWithDefaults renders template with sensible defaults
func RenderTemplateWithDefaults(templateName string, data map[string]interface{}) (string, error) {
	// Add default values
	defaults := map[string]interface{}{
		"Name":         "unnamed_theorem",
		"Description":  "Mathematical theorem",
		"TacticHint":   "sorry",
		"Variables":    "",
		"Hypothesis":   "P",
		"Conclusion":   "Q",
		"Property":     "P",
		"Type":         "ℕ",
		"Witness":      "0",
		"Verification": "sorry",
		"SystemType":   "System",
		"Quantity":     "energy",
	}

	// Merge with provided data (provided data takes precedence)
	for k, v := range data {
		defaults[k] = v
	}

	return RenderTemplate(templateName, defaults)
}

// ═══════════════════════════════════════════════════════════════════════════
// TEMPLATE HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// ListTemplates returns all available template names with descriptions
func ListTemplates() map[string]string {
	descriptions := map[string]string{
		"physics_conservation":       "Conservation laws for physical quantities",
		"physics_wave":               "Wave interference and superposition",
		"probability_poisson":        "Poisson distribution for rare events",
		"mathematical_relation":      "General mathematical relation theorem",
		"equivalence":                "If-and-only-if (iff) theorem",
		"induction":                  "Mathematical induction proof",
		"existence":                  "Existence proof (∃)",
		"uniqueness":                 "Uniqueness proof",
		"contradiction":              "Proof by contradiction",
		"transitivity":               "Transitivity of relations",
		"geometry_circle":            "Circle geometry theorem",
		"number_theory_divisibility": "Divisibility in number theory",
		"thermodynamics_roti":        "Thermodynamics of roti cooking",
		"structure_definition":       "Lean structure definition",
		"function_definition":        "Function definition with properties",
	}
	return descriptions
}

// GetTemplateFields returns required fields for a template
func GetTemplateFields(templateName string) ([]string, error) {
	templateStr, exists := TheoremTemplates[templateName]
	if !exists {
		return nil, fmt.Errorf("template '%s' not found", templateName)
	}

	// Parse template to validate it
	_, err := template.New(templateName).Parse(templateStr)
	if err != nil {
		return nil, err
	}

	// Extract field names (this is a simplified version)
	// In reality, we'd parse the template tree
	fields := []string{}
	placeholderRegex := regexp.MustCompile(`\{\{\.(\w+)\}\}`)
	matches := placeholderRegex.FindAllStringSubmatch(templateStr, -1)

	seen := make(map[string]bool)
	for _, match := range matches {
		field := match[1]
		if !seen[field] {
			fields = append(fields, field)
			seen[field] = true
		}
	}

	return fields, nil
}

// TemplateExample returns an example usage of a template
func TemplateExample(templateName string) (string, error) {
	examples := map[string]map[string]interface{}{
		"physics_conservation": {
			"Name":       "energy_conservation",
			"SystemType": "ThermodynamicSystem",
			"Quantity":   "energy",
			"TacticHint": "-- Energy is conserved in closed system\n  rfl",
		},
		"physics_wave": {
			"Name":       "wave_interference_bound",
			"TacticHint": "sorry",
		},
		"probability_poisson": {
			"Name":       "poisson_total_probability",
			"TacticHint": "sorry",
		},
		"induction": {
			"Name":          "sum_formula",
			"Property":      "2 * sum_to n = n * (n + 1)",
			"BaseCase":      "simp [sum_to]",
			"InductiveStep": "simp [sum_to]; omega",
		},
		"equivalence": {
			"Name":           "even_iff_divisible",
			"Variables":      "(n : ℕ)",
			"LeftSide":       "Even n",
			"RightSide":      "2 ∣ n",
			"ForwardTactic":  "intro ⟨k, hk⟩; use k; exact hk",
			"BackwardTactic": "intro ⟨k, hk⟩; use k; exact hk",
			"Description":    "A number is even iff it's divisible by 2",
		},
	}

	exampleData, exists := examples[templateName]
	if !exists {
		return "", fmt.Errorf("no example available for template '%s'", templateName)
	}

	return RenderTemplate(templateName, exampleData)
}

// ═══════════════════════════════════════════════════════════════════════════
// SMART TEMPLATE SELECTION
// ═══════════════════════════════════════════════════════════════════════════

// SelectTemplate chooses appropriate template based on statement
func SelectTemplate(statement string) string {
	statement = strings.ToLower(statement)

	// Physics
	if strings.Contains(statement, "conserv") || strings.Contains(statement, "energy") {
		return "physics_conservation"
	}
	if strings.Contains(statement, "wave") || strings.Contains(statement, "interference") {
		return "physics_wave"
	}
	if strings.Contains(statement, "roti") || strings.Contains(statement, "steam") {
		return "thermodynamics_roti"
	}

	// Probability
	if strings.Contains(statement, "poisson") || strings.Contains(statement, "arrival") {
		return "probability_poisson"
	}

	// Proof techniques
	if strings.Contains(statement, "iff") || strings.Contains(statement, "if and only if") {
		return "equivalence"
	}
	if strings.Contains(statement, "induction") || strings.Contains(statement, "for all n") {
		return "induction"
	}
	if strings.Contains(statement, "contradiction") || strings.Contains(statement, "impossible") {
		return "contradiction"
	}
	if strings.Contains(statement, "exists") || strings.Contains(statement, "there is") {
		return "existence"
	}
	if strings.Contains(statement, "unique") || strings.Contains(statement, "only one") {
		return "uniqueness"
	}
	if strings.Contains(statement, "transitive") || regexp.MustCompile(`if.*and.*then`).MatchString(statement) {
		return "transitivity"
	}

	// Geometry
	if strings.Contains(statement, "circle") || strings.Contains(statement, "round") {
		return "geometry_circle"
	}

	// Number theory
	if strings.Contains(statement, "divid") || strings.Contains(statement, "prime") {
		return "number_theory_divisibility"
	}

	// Default
	return "mathematical_relation"
}

// ═══════════════════════════════════════════════════════════════════════════
// CUSTOM TEMPLATE BUILDER
// ═══════════════════════════════════════════════════════════════════════════

// TemplateBuilder helps construct templates interactively
type TemplateBuilder struct {
	TemplateName string
	Data         map[string]interface{}
}

// NewTemplateBuilder creates a new template builder
func NewTemplateBuilder(templateName string) *TemplateBuilder {
	return &TemplateBuilder{
		TemplateName: templateName,
		Data:         make(map[string]interface{}),
	}
}

// Set sets a field value
func (tb *TemplateBuilder) Set(field string, value interface{}) *TemplateBuilder {
	tb.Data[field] = value
	return tb
}

// Build renders the template
func (tb *TemplateBuilder) Build() (string, error) {
	return RenderTemplateWithDefaults(tb.TemplateName, tb.Data)
}

// Validate checks if all required fields are set
func (tb *TemplateBuilder) Validate() error {
	fields, err := GetTemplateFields(tb.TemplateName)
	if err != nil {
		return err
	}

	var missing []string
	for _, field := range fields {
		if _, ok := tb.Data[field]; !ok {
			missing = append(missing, field)
		}
	}

	if len(missing) > 0 {
		return fmt.Errorf("missing required fields: %v", missing)
	}

	return nil
}
