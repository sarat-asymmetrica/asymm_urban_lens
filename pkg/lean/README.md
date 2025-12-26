# Lean 4 Bridge - Formal Mathematical Verification

A comprehensive Go library for interfacing with the Lean 4 theorem prover, translating natural language mathematical statements to formal proofs, and verifying mathematical claims.

## 🎯 Purpose

This bridge enables:
- **Formal verification** of mathematical statements in conversations
- **Natural language to Lean** translation (English → Lean 4 code)
- **Pattern-based proof generation** for common mathematical structures
- **Interactive theorem proving** sessions

## 📦 Components

### Core Bridge (`bridge.go`)
- Interface to Lean 4 theorem prover
- Proof verification and compilation
- Interactive proving sessions
- Health checking and error parsing

### Proof Patterns (`patterns.go`)
- 12 common proof patterns (conservation, transitivity, induction, etc.)
- Pattern matching from natural language triggers
- Tactic suggestions and structural analysis

### Translator (`translator.go`)
- Natural language → Lean 4 code translation
- Mathematical entity extraction
- Domain inference (physics, probability, geometry, etc.)
- Confidence scoring and suggestions

### Verifier (`verifier.go`)
- Proof verification (with/without Lean installation)
- AI-assisted verification simulation
- Proof metrics and complexity analysis
- Proof comparison and optimization suggestions

### Templates (`templates.go`)
- 15 predefined theorem templates
- Template rendering with placeholders
- Smart template selection
- Domain-specific examples

## 🚀 Quick Start

### Basic Verification

```go
import "asymm_urbanlens/pkg/lean"

// Create bridge (auto-detects Lean in PATH)
bridge := lean.NewBridge("", "./work")

// Verify a proof
proof := `
theorem energy_conservation :
  ∀ (system : ClosedSystem),
    energy system = energy system.initial := by
  intro system; rfl
`

result, err := bridge.Verify(context.Background(), proof)
if err != nil {
    log.Fatal(err)
}

if result.Valid {
    fmt.Println("✅ Proof verified!")
} else {
    fmt.Printf("❌ Errors: %v\n", result.Errors)
}
```

### Natural Language Translation

```go
// Translate natural language to Lean
statement := "Energy is conserved in closed thermodynamic systems"

context := &lean.ConversationContext{
    Domain: "physics",
    DefinedTerms: map[string]string{
        "energy": "ℝ",
    },
}

result, err := lean.TranslateToLean(statement, context)
if err != nil {
    log.Fatal(err)
}

fmt.Printf("Generated Lean code:\n%s\n", result.LeanCode)
fmt.Printf("Pattern: %s (confidence: %.1f%%)\n",
    result.Pattern.Name, result.Confidence*100)
fmt.Printf("Suggestions: %v\n", result.Suggestions)
```

### Using Proof Patterns

```go
// Find appropriate pattern
pattern := lean.SelectPatternForInsight(
    "If A > B and B > C then A > C",
)

fmt.Printf("Pattern: %s\n", pattern.Name)
fmt.Printf("Template:\n%s\n", pattern.Template)
fmt.Printf("Example:\n%s\n", pattern.Example)

// Get all patterns matching triggers
patterns := lean.SelectPatternsByTriggers("conserved energy")
for _, p := range patterns {
    fmt.Printf("- %s: %s\n", p.Name, p.Description)
}
```

### Using Templates

```go
// Render a template
code, err := lean.RenderTemplate("physics_conservation", map[string]interface{}{
    "Name":       "energy_conservation",
    "SystemType": "ThermodynamicSystem",
    "Quantity":   "energy",
    "TacticHint": "intro system; rfl",
})

fmt.Println(code)

// Smart template selection
templateName := lean.SelectTemplate(
    "Energy is conserved in closed systems",
)
// Returns: "physics_conservation"

// List all templates
templates := lean.ListTemplates()
for name, description := range templates {
    fmt.Printf("%s: %s\n", name, description)
}
```

## 🧪 Example Proofs

The library includes four complete proof files demonstrating real-world applications:

### 1. Thermodynamics (`proofs/thermodynamics.lean`)
**Why covering roti prevents steam formation**
- Energy calculations (heating + vaporization)
- Latent heat dominance (2260 J/g >> heating energy)
- Vapor pressure and coverage effects
- Conservation in closed systems

Key theorem:
```lean
theorem roti_covering_principle :
  ∀ (system : RotiSystem),
    system.is_covered = true →
    vapor_pressure (system.temp + 10) > vapor_pressure system.temp
```

### 2. Wave Mechanics (`proofs/wave_mechanics.lean`)
**Wave interference and superposition**
- Constructive interference (in-phase → amplitudes add)
- Destructive interference (out-of-phase → cancellation)
- Intensity formula with phase difference
- Applications: noise-canceling, soap bubbles, radio dead zones

Key theorem:
```lean
theorem interference_intensity (w1 w2 : Wave) :
  intensity (w1 + w2) =
    intensity w1 + intensity w2 +
    2 * √(intensity w1 * intensity w2) * cos(phase_diff w1 w2)
```

### 3. Probability (`proofs/probability.lean`)
**Poisson distribution for rare events**
- PMF validation (non-negative, sums to 1)
- Mean = Variance = λ
- Binomial → Poisson limit
- Connection to exponential waiting times

Key theorem:
```lean
theorem poisson_predictable_aggregate :
  -- Relative error decreases as 1/√(nλ)
  relative_std = 1 / √(n * λ)
```

### 4. Geometry (`proofs/geometry.lean`)
**Why the Moon is round**
- Sphere minimizes surface area for given volume
- Hydrostatic equilibrium requires spherical surfaces
- Minimum energy configuration
- Critical mass threshold (~5×10²⁰ kg)

Key theorem:
```lean
theorem large_bodies_become_spherical :
  body.mass > critical_mass →
  equilibrium_shape = is_sphere
```

## 📚 Proof Patterns Library

The library includes 12 common proof patterns:

| Pattern | Triggers | Use Case |
|---------|----------|----------|
| `conservation` | "conserved", "invariant", "preserved" | Physical conservation laws |
| `transitivity` | "if...and...then", "chains" | Transitive relations |
| `induction` | "for all n", "base case" | Mathematical induction |
| `contradiction` | "impossible", "leads to" | Proof by contradiction |
| `construction` | "there exists", "we can build" | Constructive existence |
| `equivalence` | "if and only if", "iff" | Biconditional statements |
| `cases` | "either...or", "case by case" | Case analysis |
| `uniqueness` | "unique", "only one" | Uniqueness proofs |
| `pigeonhole` | "more...than", "collision" | Pigeonhole principle |
| `continuity` | "continuous", "smooth" | Analysis/continuity |
| `physics_wave` | "wave", "interference" | Wave mechanics |
| `probability_poisson` | "poisson", "arrival rate" | Poisson processes |

## 🔧 Advanced Features

### AI-Assisted Verification (No Lean Required!)

```go
// Use AI to simulate verification when Lean not installed
aiClient := // your AI client implementation

result, err := lean.SimulateVerification(leanCode, aiClient)
// Returns same VerificationResult interface
```

### Proof Metrics

```go
metrics := lean.AnalyzeProof(leanCode)

fmt.Printf("Lines: %d\n", metrics.LineCount)
fmt.Printf("Tactics: %d (%v)\n",
    metrics.TacticCount, metrics.UsedTactics)
fmt.Printf("Complexity: %.2f\n", metrics.ComplexityScore)
```

### Proof Comparison

```go
comparison := lean.CompareProofs(proof1, proof2)

fmt.Printf("Simpler proof: %d\n", comparison.SimplerProof)
fmt.Printf("Recommendation: %s\n", comparison.Recommendation)
fmt.Printf("Unique tactics in proof 1: %v\n",
    comparison.UniqueTactics1)
```

### Interactive Sessions

```go
session, err := bridge.Interactive(ctx)
defer session.Close()

// Send commands
session.Send("theorem test : 2 + 2 = 4 := by")
session.Send("  norm_num")

// Read responses
response, _ := session.Read()
fmt.Println(response)
```

## 🎓 Mathematical Domains Supported

The translator automatically infers domain and adds appropriate imports:

- **Physics**: `Mathlib.Analysis.SpecialFunctions.Exp`
- **Probability**: `Mathlib.Probability.Distributions.Poisson`
- **Geometry**: `Mathlib.Geometry.Euclidean.Basic`
- **Algebra**: `Mathlib.Algebra.Group.Defs`
- **Analysis**: `Mathlib.Analysis.Calculus.Deriv.Basic`
- **Number Theory**: `Mathlib.NumberTheory.Divisors`

## 🧪 Testing

Run the comprehensive test suite:

```bash
cd pkg/lean
go test -v
```

Benchmarks:
```bash
go test -bench=. -benchmem
```

## 📖 Example Workflows

### 1. Restaurant Capacity Planning (Poisson)

```go
statement := "Average 20 customers per hour arrive following Poisson"
result, _ := lean.TranslateToLean(statement, &lean.ConversationContext{
    Domain: "probability",
})

// Generates Poisson distribution theorem
// Can verify staffing calculations are mathematically sound
```

### 2. Physics Conservation (Thermodynamics)

```go
statement := "When roti is covered, heat cannot escape and steam formation is prevented"
result, _ := lean.TranslateToLean(statement, &lean.ConversationContext{
    Domain: "physics",
})

// Generates conservation theorem with closed system
// Can verify energy calculations
```

### 3. Wave Interference (Optics)

```go
statement := "Two waves of same frequency interfere constructively when in phase"
result, _ := lean.TranslateToLean(statement, &lean.ConversationContext{
    Domain: "physics",
})

// Generates wave superposition theorem
// Can verify amplitude calculations
```

## 🎯 Integration with Conversation System

This Lean bridge is designed to integrate with the `pkg/conversation` system:

```go
// In persona handler
if insight.RequiresFormalVerification {
    leanCode, _ := lean.TranslateToLean(insight.Statement, conversationCtx)

    result, _ := bridge.Verify(ctx, leanCode)

    insight.FormalProof = leanCode
    insight.ProofValid = result.Valid
    insight.Confidence *= result.Confidence
}
```

## 🔮 Future Enhancements

- [ ] Lean 4 LSP integration for real-time feedback
- [ ] Proof search automation
- [ ] Tactic learning from successful proofs
- [ ] Multi-step proof decomposition
- [ ] Graphical proof visualization
- [ ] Integration with Mathlib search
- [ ] Custom tactic development

## 📚 References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/)

## 🙏 Philosophy

> "Mathematics is the art of giving the same name to different things." — Henri Poincaré

This library brings formal mathematical rigor to natural conversations about the physical world. Whether discussing roti, restaurant customers, or celestial bodies, the underlying mathematics deserves verification.

**May all insights be verified! Om Lokah Samastah Sukhino Bhavantu!** 🙏
