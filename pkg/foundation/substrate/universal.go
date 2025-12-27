// Package substrate implements the Universal S³ Substrate
// The unified mathematical core for SAT, Navier-Stokes, and Quantum engines.
//
// "One equation to rule them all."
// ∂Φ/∂t = Φ ⊗ Φ + C(domain)
//
// Built with LOVE × SIMPLICITY × TRUTH × JOY
package substrate

import (
	"math"
	"math/rand"
)

// ============================================================================
// UNIVERSAL CONSTANTS
// ============================================================================

const (
	GoldenRatio = 1.618033988749895
	TeslaFreq   = 432.0 // Hz
	VedicScale  = 108   // Sacred number
)

// ============================================================================
// QUATERNION PRIMITIVES (S³ Geometry)
// ============================================================================

// Quaternion represents a point on the S³ hypersphere.
type Quaternion struct {
	W, X, Y, Z float64
}

// NewQuaternion creates a new quaternion.
func NewQuaternion(w, x, y, z float64) Quaternion {
	return Quaternion{W: w, X: x, Y: y, Z: z}
}

// RandomQuaternion returns a uniform random quaternion on S³.
func RandomQuaternion() Quaternion {
	// Marsaglia's method or similar for uniform S³
	u1 := rand.Float64()
	u2 := rand.Float64()
	u3 := rand.Float64()

	w := math.Sqrt(1-u1) * math.Sin(2*math.Pi*u2)
	x := math.Sqrt(1-u1) * math.Cos(2*math.Pi*u2)
	y := math.Sqrt(u1) * math.Sin(2*math.Pi*u3)
	z := math.Sqrt(u1) * math.Cos(2*math.Pi*u3)

	return NewQuaternion(w, x, y, z)
}

// Norm computes the Euclidean norm (length).
func (q Quaternion) Norm() float64 {
	return math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
}

// Normalize returns the unit quaternion.
func (q Quaternion) Normalize() Quaternion {
	n := q.Norm()
	if n < 1e-10 {
		return NewQuaternion(1, 0, 0, 0) // Identity backup
	}
	return NewQuaternion(q.W/n, q.X/n, q.Y/n, q.Z/n)
}

// Dot product (similarity metric).
func (q Quaternion) Dot(p Quaternion) float64 {
	return q.W*p.W + q.X*p.X + q.Y*p.Y + q.Z*p.Z
}

// Mul performs quaternion multiplication (Hamilton product).
// Non-commutative! represents interaction/entanglement.
func (q Quaternion) Mul(p Quaternion) Quaternion {
	return NewQuaternion(
		q.W*p.W-q.X*p.X-q.Y*p.Y-q.Z*p.Z,
		q.W*p.X+q.X*p.W+q.Y*p.Z-q.Z*p.Y,
		q.W*p.Y-q.X*p.Z+q.Y*p.W+q.Z*p.X,
		q.W*p.Z+q.X*p.Y-q.Y*p.X+q.Z*p.W,
	)
}

// Add adds two quaternions.
func (q Quaternion) Add(p Quaternion) Quaternion {
	return NewQuaternion(q.W+p.W, q.X+p.X, q.Y+p.Y, q.Z+p.Z)
}

// Scale scales the quaternion.
func (q Quaternion) Scale(s float64) Quaternion {
	return NewQuaternion(q.W*s, q.X*s, q.Y*s, q.Z*s)
}

// SLERP (Spherical Linear Interpolation)
// The universal evolution operator along geodesics.
func SLERP(q0, q1 Quaternion, t float64) Quaternion {
	dot := q0.Dot(q1)

	// Antipodal adjustment (take shortest path)
	if dot < 0 {
		q1 = q1.Scale(-1.0)
		dot = -dot
	}

	// Linear fallback for closeness
	if dot > 0.9995 {
		result := q0.Add(q1.Add(q0.Scale(-1.0)).Scale(t))
		return result.Normalize()
	}

	theta := math.Acos(dot)
	sinTheta := math.Sin(theta)

	w0 := math.Sin((1-t)*theta) / sinTheta
	w1 := math.Sin(t*theta) / sinTheta

	return q0.Scale(w0).Add(q1.Scale(w1))
}

// ============================================================================
// UNIVERSAL INTERFACES
// ============================================================================

// PhiState is the interface for any entity in the universe.
// Whether it's a SAT variable, a fluid voxel, or a qubit.
type PhiState interface {
	// GetQuaternion returns the S³ state representation.
	GetQuaternion() Quaternion

	// SetQuaternion updates the S³ state.
	SetQuaternion(q Quaternion)

	// GetRegime returns the current dynamic regime (R1/R2/R3).
	GetRegime() Regime
}

// ContextFunction represents C(domain) in the universal equation.
// It calculates the "target" or "force" acting on the state.
type ContextFunction interface {
	// CalculateTarget determines where the state *wants* to go based on domain constraints.
	CalculateTarget(state PhiState, neighbors []PhiState, globals interface{}) Quaternion

	// CalculateInteraction computes Φ ⊗ Φ term (entanglement/interaction).
	CalculateInteraction(state PhiState, neighbors []PhiState) Quaternion
}

// Regime represents the three-regime dynamics.
type Regime int

const (
	R1_Exploration  Regime = iota // High entropy, search
	R2_Optimization               // Maximum complexity, phase transition
	R3_Stabilization              // Low entropy, convergence
)

func (r Regime) String() string {
	switch r {
	case R1_Exploration:
		return "R1 (Exploration)"
	case R2_Optimization:
		return "R2 (Optimization)"
	case R3_Stabilization:
		return "R3 (Stabilization)"
	default:
		return "Unknown"
	}
}

// ============================================================================
// UNIVERSAL SOLVER ENGINE
// ============================================================================

// SolverConfig holds configuration for the universal solver.
type SolverConfig struct {
	TimeStep    float64
	Temperature float64 // For annealing/regime control
	BatchSize   int     // Williams batching
}

// UniversalSolver drives the evolution of a system.
type UniversalSolver struct {
	States  []PhiState
	Context ContextFunction
	Config  SolverConfig
	Globals interface{} // Domain-specific global data (e.g., SAT clauses)
	Time    float64
	Iteration int
}

// NewUniversalSolver creates a new solver instance.
func NewUniversalSolver(states []PhiState, ctx ContextFunction, cfg SolverConfig, globals interface{}) *UniversalSolver {
	return &UniversalSolver{
		States:  states,
		Context: ctx,
		Config:  cfg,
		Globals: globals,
		Time:    0.0,
		Iteration: 0,
	}
}

// Evolve performs one time step of the universal equation.
// ∂Φ/∂t = Φ ⊗ Φ + C(domain)
// Implementation: Φ(t+dt) = SLERP(Φ(t), Target, strength)
func (s *UniversalSolver) Evolve() {
	dt := s.Config.TimeStep

	// Williams Batching Logic could go here for massive scale.
	// For simplicity in this v1, we iterate linearly (or could parallelize).

	// We need a buffer to store next states to avoid sequential dependency bias within one step
	// (Simulating simultaneous update)
	nextQuats := make([]Quaternion, len(s.States))

	for i, state := range s.States {
		currentQ := state.GetQuaternion()

		// 1. Calculate Interaction (Φ ⊗ Φ)
		interactionQ := s.Context.CalculateInteraction(state, nil)

		// 2. Calculate Context Target C(domain)
		targetQ := s.Context.CalculateTarget(state, nil, s.Globals)

		// 3. Update Regime (Temperature control)
		// We use a stronger projection as temperature drops
		foldStrength := 2.0 / (1.0 + s.Config.Temperature) // Modified strength function

		// Apply Interaction effect (e.g. rotation)
		effectiveQ := currentQ.Mul(interactionQ)

		// 4. Evolve via SLERP (The Universal Operator)
		// Move current state towards target state
		// Use a fixed rate * dt * strength
		nextQ := SLERP(effectiveQ, targetQ, foldStrength*dt*5.0) // Increased scalar for convergence
		nextQuats[i] = nextQ
	}

	// Apply updates
	for i, state := range s.States {
		state.SetQuaternion(nextQuats[i])
	}

	// Global updates (cooling, time)
	s.Time += dt
	s.Iteration++

	// Basic cooling (Regime transition simulation)
	if s.Config.Temperature > 0.05 {
		s.Config.Temperature *= 0.95 // Faster cooling for test
	}
}

// GetSystemEntropy calculates Shannon entropy of the system state distribution.
// Useful for regime detection.
func (s *UniversalSolver) GetSystemEntropy() float64 {
	// Discretize S³ into buckets or use mean distance from centroid
	// Simple proxy: 1 - mean(alignment with centroid)

	if len(s.States) == 0 {
		return 0
	}

	centroid := NewQuaternion(0, 0, 0, 0)
	for _, state := range s.States {
		centroid = centroid.Add(state.GetQuaternion())
	}
	centroid = centroid.Normalize()

	totalDot := 0.0
	for _, state := range s.States {
		totalDot += math.Abs(state.GetQuaternion().Dot(centroid))
	}
	meanAlignment := totalDot / float64(len(s.States))

	// Entropy proxy: 0 when all aligned, high when disordered
	return 1.0 - meanAlignment
}

// DetectRegime determines the global regime based on entropy/dynamics.
func (s *UniversalSolver) DetectRegime() Regime {
	entropy := s.GetSystemEntropy()
	return ClassifyRegime(entropy)
}

// ============================================================================
// THREE-REGIME MONITOR (Standalone)
// ============================================================================

// ClassifyRegime classifies a metric (like entropy 0.0-1.0) into a Regime.
func ClassifyRegime(metric float64) Regime {
	// Thresholds derived from "Three-Regime Dynamics"
	// R1 (Exploration): High entropy/variance > 0.4
	// R2 (Optimization): Medium entropy/variance 0.1 - 0.4
	// R3 (Stabilization): Low entropy/variance < 0.1
	if metric > 0.4 {
		return R1_Exploration
	} else if metric > 0.1 {
		return R2_Optimization
	}
	return R3_Stabilization
}

// ThreeRegimeMonitor tracks the history of regimes to ensure stability.
type ThreeRegimeMonitor struct {
	History []Regime
}

func NewThreeRegimeMonitor() *ThreeRegimeMonitor {
	return &ThreeRegimeMonitor{
		History: make([]Regime, 0),
	}
}

// AddObservation adds a new metric observation and returns the regime.
func (m *ThreeRegimeMonitor) AddObservation(metric float64) Regime {
	regime := ClassifyRegime(metric)
	m.History = append(m.History, regime)
	return regime
}

// IsConverged checks if the system has settled into R3 (Stabilization).
func (m *ThreeRegimeMonitor) IsConverged(windowSize int) bool {
	if len(m.History) < windowSize {
		return false
	}

	// Check last 'windowSize' entries
	start := len(m.History) - windowSize
	for i := start; i < len(m.History); i++ {
		if m.History[i] != R3_Stabilization {
			return false
		}
	}
	return true
}

// SingularityRisk checks if the system is in a dangerous state (R2 < 15% equivalent).
// Here we use a metric check.
func SingularityRisk(r3_percentage float64) string {
	if r3_percentage < 0.50 {
		return "EMERGENCY" // < 50% R3 means instability
	} else if r3_percentage < 0.55 {
		return "WARNING"
	}
	return "OK"
}
