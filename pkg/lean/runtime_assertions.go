// Package lean - Runtime Proof Assertions
// Bridges formal Lean proofs to actual Go runtime validation
//
// "Tests are instances. Runtime assertions bridge proofs to practice." - Mirzakhani
//
// These assertions validate that proof assumptions hold during execution:
// - Quaternion norm preservation (||Q|| = 1.0 ± ε)
// - S³ membership after SLERP
// - Hamilton multiplication closure
// - Digital root partitioning
// - Williams space bounds
package lean

import (
	"fmt"
	"math"
)

// ═══════════════════════════════════════════════════════════════════════════
// CORE ASSERTION INTERFACE
// ═══════════════════════════════════════════════════════════════════════════

// ProofAssertion represents a runtime validation of a formal proof
// Each assertion corresponds to a Lean theorem and validates its assumptions hold
type ProofAssertion interface {
	// Name returns the assertion identifier
	Name() string

	// Theorem returns the Lean theorem this validates
	Theorem() string

	// Validate checks if the assertion holds for given data
	// Returns nil if assertion passes, error describing violation otherwise
	Validate(data interface{}) error

	// Severity returns the importance level
	Severity() AssertionSeverity

	// Description returns human-readable explanation
	Description() string
}

// AssertionSeverity indicates how critical a violation is
type AssertionSeverity int

const (
	// SeverityInfo - Informational, expected to sometimes fail
	SeverityInfo AssertionSeverity = iota

	// SeverityWarning - Should investigate but not fatal
	SeverityWarning

	// SeverityCritical - Fundamental invariant violated, execution suspect
	SeverityCritical
)

func (s AssertionSeverity) String() string {
	switch s {
	case SeverityInfo:
		return "INFO"
	case SeverityWarning:
		return "WARNING"
	case SeverityCritical:
		return "CRITICAL"
	default:
		return "UNKNOWN"
	}
}

// AssertionResult captures the result of running an assertion
type AssertionResult struct {
	AssertionName string            `json:"assertion_name"`
	Theorem       string            `json:"theorem"`
	Passed        bool              `json:"passed"`
	Error         string            `json:"error,omitempty"`
	Severity      AssertionSeverity `json:"severity"`
	Data          interface{}       `json:"data,omitempty"` // Optional: data that was validated
}

// ═══════════════════════════════════════════════════════════════════════════
// BASE ASSERTION (Common Implementation)
// ═══════════════════════════════════════════════════════════════════════════

// BaseAssertion provides common fields for all assertions
type BaseAssertion struct {
	name        string
	theorem     string
	severity    AssertionSeverity
	description string
}

func (a *BaseAssertion) Name() string                  { return a.name }
func (a *BaseAssertion) Theorem() string               { return a.theorem }
func (a *BaseAssertion) Severity() AssertionSeverity   { return a.severity }
func (a *BaseAssertion) Description() string           { return a.description }

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION 1: Quaternion Norm Preservation
// Validates: ||Q|| = 1.0 ± ε
// Lean Theorem: quaternion_norm_unit
// ═══════════════════════════════════════════════════════════════════════════

// QuaternionNormAssertion validates quaternion stays on S³ (unit 3-sphere)
type QuaternionNormAssertion struct {
	BaseAssertion
	Epsilon float64 // Tolerance for floating-point comparison
}

// NewQuaternionNormAssertion creates assertion with default epsilon (1e-6)
func NewQuaternionNormAssertion() *QuaternionNormAssertion {
	return NewQuaternionNormAssertionWithEpsilon(1e-6)
}

// NewQuaternionNormAssertionWithEpsilon creates assertion with custom tolerance
func NewQuaternionNormAssertionWithEpsilon(epsilon float64) *QuaternionNormAssertion {
	return &QuaternionNormAssertion{
		BaseAssertion: BaseAssertion{
			name:        "QuaternionNormPreservation",
			theorem:     "quaternion_norm_unit",
			severity:    SeverityCritical,
			description: "Validates quaternion remains on unit 3-sphere: ||Q|| = 1.0 ± ε",
		},
		Epsilon: epsilon,
	}
}

// QuaternionData represents a quaternion for validation
type QuaternionData struct {
	W, X, Y, Z float64
	Label      string // Optional: for debugging
}

// Norm computes quaternion norm
func (q QuaternionData) Norm() float64 {
	return math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
}

func (a *QuaternionNormAssertion) Validate(data interface{}) error {
	q, ok := data.(*QuaternionData)
	if !ok {
		return fmt.Errorf("expected *QuaternionData, got %T", data)
	}

	norm := q.Norm()

	// Check for NaN/Inf
	if math.IsNaN(norm) || math.IsInf(norm, 0) {
		return fmt.Errorf("quaternion norm is NaN or Inf: %v (Q=%v)", norm, q)
	}

	// Check unit norm within epsilon
	deviation := math.Abs(norm - 1.0)
	if deviation > a.Epsilon {
		label := q.Label
		if label == "" {
			label = fmt.Sprintf("Q(%.4f,%.4f,%.4f,%.4f)", q.W, q.X, q.Y, q.Z)
		}
		return fmt.Errorf("quaternion norm deviation: ||%s|| = %.8f, expected 1.0 ± %.2e (deviation: %.2e)",
			label, norm, a.Epsilon, deviation)
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION 2: SLERP Preserves S³
// Validates: All waypoints on geodesic remain on unit sphere
// Lean Theorem: slerp_preserves_s3
// ═══════════════════════════════════════════════════════════════════════════

// SLERPPreservesS3Assertion validates SLERP waypoints stay on S³
type SLERPPreservesS3Assertion struct {
	BaseAssertion
	Epsilon float64
}

// NewSLERPPreservesS3Assertion creates SLERP preservation assertion
func NewSLERPPreservesS3Assertion() *SLERPPreservesS3Assertion {
	return NewSLERPPreservesS3AssertionWithEpsilon(1e-6)
}

// NewSLERPPreservesS3AssertionWithEpsilon creates assertion with custom epsilon
func NewSLERPPreservesS3AssertionWithEpsilon(epsilon float64) *SLERPPreservesS3Assertion {
	return &SLERPPreservesS3Assertion{
		BaseAssertion: BaseAssertion{
			name:        "SLERPPreservesS3",
			theorem:     "slerp_preserves_s3",
			severity:    SeverityCritical,
			description: "Validates SLERP interpolation keeps all waypoints on unit 3-sphere",
		},
		Epsilon: epsilon,
	}
}

// SLERPData represents a SLERP operation to validate
type SLERPData struct {
	Q0       QuaternionData
	Q1       QuaternionData
	Waypoint QuaternionData // Result of SLERP(Q0, Q1, t) for some t
	T        float64        // Interpolation parameter
}

func (a *SLERPPreservesS3Assertion) Validate(data interface{}) error {
	slerp, ok := data.(*SLERPData)
	if !ok {
		return fmt.Errorf("expected *SLERPData, got %T", data)
	}

	// Validate endpoints
	normAssertion := NewQuaternionNormAssertionWithEpsilon(a.Epsilon)

	if err := normAssertion.Validate(&slerp.Q0); err != nil {
		return fmt.Errorf("SLERP start point Q0 invalid: %w", err)
	}

	if err := normAssertion.Validate(&slerp.Q1); err != nil {
		return fmt.Errorf("SLERP end point Q1 invalid: %w", err)
	}

	// Validate waypoint
	if err := normAssertion.Validate(&slerp.Waypoint); err != nil {
		return fmt.Errorf("SLERP waypoint at t=%.4f invalid: %w", slerp.T, err)
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION 3: Hamilton Multiplication Closure
// Validates: Q1 * Q2 ∈ S³ (product stays on sphere)
// Lean Theorem: hamilton_multiplication_closure
// ═══════════════════════════════════════════════════════════════════════════

// HamiltonClosureAssertion validates quaternion multiplication closure
type HamiltonClosureAssertion struct {
	BaseAssertion
	Epsilon float64
}

// NewHamiltonClosureAssertion creates Hamilton closure assertion
func NewHamiltonClosureAssertion() *HamiltonClosureAssertion {
	return NewHamiltonClosureAssertionWithEpsilon(1e-6)
}

// NewHamiltonClosureAssertionWithEpsilon creates assertion with custom epsilon
func NewHamiltonClosureAssertionWithEpsilon(epsilon float64) *HamiltonClosureAssertion {
	return &HamiltonClosureAssertion{
		BaseAssertion: BaseAssertion{
			name:        "HamiltonMultiplicationClosure",
			theorem:     "hamilton_multiplication_closure",
			severity:    SeverityCritical,
			description: "Validates quaternion multiplication preserves S³: Q1 * Q2 ∈ S³",
		},
		Epsilon: epsilon,
	}
}

// MultiplicationData represents a quaternion multiplication to validate
type MultiplicationData struct {
	Q1     QuaternionData
	Q2     QuaternionData
	Result QuaternionData
}

func (a *HamiltonClosureAssertion) Validate(data interface{}) error {
	mult, ok := data.(*MultiplicationData)
	if !ok {
		return fmt.Errorf("expected *MultiplicationData, got %T", data)
	}

	normAssertion := NewQuaternionNormAssertionWithEpsilon(a.Epsilon)

	// Validate inputs
	if err := normAssertion.Validate(&mult.Q1); err != nil {
		return fmt.Errorf("multiplication operand Q1 invalid: %w", err)
	}

	if err := normAssertion.Validate(&mult.Q2); err != nil {
		return fmt.Errorf("multiplication operand Q2 invalid: %w", err)
	}

	// Validate result
	if err := normAssertion.Validate(&mult.Result); err != nil {
		return fmt.Errorf("multiplication result invalid: %w", err)
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION 4: Digital Root Partition
// Validates: dr(n) ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9}
// Lean Theorem: digital_root_partition
// ═══════════════════════════════════════════════════════════════════════════

// DigitalRootPartitionAssertion validates digital root values
type DigitalRootPartitionAssertion struct {
	BaseAssertion
}

// NewDigitalRootPartitionAssertion creates digital root assertion
func NewDigitalRootPartitionAssertion() *DigitalRootPartitionAssertion {
	return &DigitalRootPartitionAssertion{
		BaseAssertion: BaseAssertion{
			name:        "DigitalRootPartition",
			theorem:     "digital_root_partition",
			severity:    SeverityCritical,
			description: "Validates digital root is in range [1..9] for non-zero inputs",
		},
	}
}

// DigitalRootData represents a digital root computation
type DigitalRootData struct {
	Input        int64
	DigitalRoot  int64
	ExpectedZero bool // True if input is 0 (dr should be 0)
}

func (a *DigitalRootPartitionAssertion) Validate(data interface{}) error {
	dr, ok := data.(*DigitalRootData)
	if !ok {
		return fmt.Errorf("expected *DigitalRootData, got %T", data)
	}

	// Special case: dr(0) = 0
	if dr.ExpectedZero {
		if dr.DigitalRoot != 0 {
			return fmt.Errorf("digital root of 0 should be 0, got %d", dr.DigitalRoot)
		}
		return nil
	}

	// Non-zero: dr ∈ {1..9}
	if dr.DigitalRoot < 1 || dr.DigitalRoot > 9 {
		return fmt.Errorf("digital root of %d is %d, expected ∈ [1..9]",
			dr.Input, dr.DigitalRoot)
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION 5: Williams Space Bound
// Validates: space ≤ √t × log₂(t)
// Lean Theorem: williams_space_bound
// ═══════════════════════════════════════════════════════════════════════════

// WilliamsSpaceBoundAssertion validates Williams batching space complexity
type WilliamsSpaceBoundAssertion struct {
	BaseAssertion
	SafetyFactor float64 // Allow small violations (e.g., 1.05 = 5% over budget)
}

// NewWilliamsSpaceBoundAssertion creates Williams space bound assertion
func NewWilliamsSpaceBoundAssertion() *WilliamsSpaceBoundAssertion {
	return NewWilliamsSpaceBoundAssertionWithSafety(1.05)
}

// NewWilliamsSpaceBoundAssertionWithSafety creates assertion with custom safety factor
func NewWilliamsSpaceBoundAssertionWithSafety(safetyFactor float64) *WilliamsSpaceBoundAssertion {
	return &WilliamsSpaceBoundAssertion{
		BaseAssertion: BaseAssertion{
			name:        "WilliamsSpaceBound",
			theorem:     "williams_space_bound",
			severity:    SeverityWarning, // Warning, not critical (small overruns tolerable)
			description: "Validates Williams batching space usage: space ≤ √t × log₂(t)",
		},
		SafetyFactor: safetyFactor,
	}
}

// WilliamsData represents a Williams batching operation
type WilliamsData struct {
	T            int64 // Total items processed
	SpaceUsed    int64 // Actual space used (e.g., batch size)
	ExpectedBound int64 // Theoretical bound: ceil(√t × log₂(t))
}

func (a *WilliamsSpaceBoundAssertion) Validate(data interface{}) error {
	w, ok := data.(*WilliamsData)
	if !ok {
		return fmt.Errorf("expected *WilliamsData, got %T", data)
	}

	// Compute bound with safety factor
	bound := float64(w.ExpectedBound) * a.SafetyFactor

	if float64(w.SpaceUsed) > bound {
		return fmt.Errorf("Williams space bound violated: used %d, expected ≤ %d (bound: %.2f × safety %.2f), t=%d",
			w.SpaceUsed, w.ExpectedBound, bound, a.SafetyFactor, w.T)
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION 6: Three-Regime Stability
// Validates: R3 ≥ 50% (stable regime dominates)
// Lean Theorem: three_regime_stability
// ═══════════════════════════════════════════════════════════════════════════

// ThreeRegimeStabilityAssertion validates three-regime dynamics
type ThreeRegimeStabilityAssertion struct {
	BaseAssertion
	MinR3 float64 // Minimum required R3 (default: 0.50)
}

// NewThreeRegimeStabilityAssertion creates three-regime stability assertion
func NewThreeRegimeStabilityAssertion() *ThreeRegimeStabilityAssertion {
	return NewThreeRegimeStabilityAssertionWithMinR3(0.50)
}

// NewThreeRegimeStabilityAssertionWithMinR3 creates assertion with custom min R3
func NewThreeRegimeStabilityAssertionWithMinR3(minR3 float64) *ThreeRegimeStabilityAssertion {
	return &ThreeRegimeStabilityAssertion{
		BaseAssertion: BaseAssertion{
			name:        "ThreeRegimeStability",
			theorem:     "three_regime_stability",
			severity:    SeverityCritical,
			description: "Validates R3 (stabilization) ≥ 50% to prevent singularity",
		},
		MinR3: minR3,
	}
}

// ThreeRegimeData represents three-regime state
type ThreeRegimeData struct {
	R1    float64 // Exploration
	R2    float64 // Optimization
	R3    float64 // Stabilization
	Label string  // Optional: context
}

func (a *ThreeRegimeStabilityAssertion) Validate(data interface{}) error {
	regime, ok := data.(*ThreeRegimeData)
	if !ok {
		return fmt.Errorf("expected *ThreeRegimeData, got %T", data)
	}

	// Check normalization
	sum := regime.R1 + regime.R2 + regime.R3
	if math.Abs(sum-1.0) > 1e-6 {
		return fmt.Errorf("regime not normalized: R1+R2+R3 = %.8f, expected 1.0", sum)
	}

	// Check stability
	if regime.R3 < a.MinR3 {
		label := regime.Label
		if label == "" {
			label = fmt.Sprintf("(%.2f, %.2f, %.2f)", regime.R1, regime.R2, regime.R3)
		}
		return fmt.Errorf("regime %s unstable: R3 = %.4f < %.4f (SINGULARITY RISK)",
			label, regime.R3, a.MinR3)
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION REGISTRY
// Provides centralized access to all assertions
// ═══════════════════════════════════════════════════════════════════════════

// AssertionRegistry manages all runtime assertions
type AssertionRegistry struct {
	assertions map[string]ProofAssertion
}

// NewAssertionRegistry creates registry with all standard assertions
func NewAssertionRegistry() *AssertionRegistry {
	registry := &AssertionRegistry{
		assertions: make(map[string]ProofAssertion),
	}

	// Register standard assertions
	registry.Register(NewQuaternionNormAssertion())
	registry.Register(NewSLERPPreservesS3Assertion())
	registry.Register(NewHamiltonClosureAssertion())
	registry.Register(NewDigitalRootPartitionAssertion())
	registry.Register(NewWilliamsSpaceBoundAssertion())
	registry.Register(NewThreeRegimeStabilityAssertion())

	return registry
}

// Register adds an assertion to the registry
func (r *AssertionRegistry) Register(assertion ProofAssertion) {
	r.assertions[assertion.Name()] = assertion
}

// Get retrieves assertion by name
func (r *AssertionRegistry) Get(name string) (ProofAssertion, bool) {
	assertion, ok := r.assertions[name]
	return assertion, ok
}

// All returns all registered assertions
func (r *AssertionRegistry) All() []ProofAssertion {
	assertions := make([]ProofAssertion, 0, len(r.assertions))
	for _, a := range r.assertions {
		assertions = append(assertions, a)
	}
	return assertions
}

// Count returns number of registered assertions
func (r *AssertionRegistry) Count() int {
	return len(r.assertions)
}
