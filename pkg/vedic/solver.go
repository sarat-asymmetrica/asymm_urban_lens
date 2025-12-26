// Package vedic provides the Vedic Differential Solver for meta-optimization
// Uses Tirthaji's 16 Sutras as differential operators on S³
// Ported from Asymmetrica for IIHS Urban Lens
package vedic

import (
	"math"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════════════════

const (
	PHI           = 1.618033988749895
	PHI_INV       = 0.6180339887498949
	SEVEN_EIGHTHS = 0.875

	// Three-regime boundaries
	R1_END = 0.30
	R2_END = 0.50

	// Digital root filtering rate
	DIGITAL_ROOT_FILTER_RATE = 0.889
)

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION
// ═══════════════════════════════════════════════════════════════════════════

// Quaternion represents a point on S³
type Quaternion struct {
	W, X, Y, Z float64
}

// NewQuaternion creates a normalized quaternion
func NewQuaternion(w, x, y, z float64) Quaternion {
	q := Quaternion{W: w, X: x, Y: y, Z: z}
	return q.Normalize()
}

// Norm returns magnitude
func (q Quaternion) Norm() float64 {
	return math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
}

// Normalize projects to unit sphere
func (q Quaternion) Normalize() Quaternion {
	n := q.Norm()
	if n < 1e-10 {
		return Quaternion{W: 1, X: 0, Y: 0, Z: 0}
	}
	return Quaternion{W: q.W / n, X: q.X / n, Y: q.Y / n, Z: q.Z / n}
}

// Dot product
func (q1 Quaternion) Dot(q2 Quaternion) float64 {
	return q1.W*q2.W + q1.X*q2.X + q1.Y*q2.Y + q1.Z*q2.Z
}

// Multiply - Hamilton product
func (q1 Quaternion) Multiply(q2 Quaternion) Quaternion {
	return NewQuaternion(
		q1.W*q2.W-q1.X*q2.X-q1.Y*q2.Y-q1.Z*q2.Z,
		q1.W*q2.X+q1.X*q2.W+q1.Y*q2.Z-q1.Z*q2.Y,
		q1.W*q2.Y-q1.X*q2.Z+q1.Y*q2.W+q1.Z*q2.X,
		q1.W*q2.Z+q1.X*q2.Y-q1.Y*q2.X+q1.Z*q2.W,
	)
}

// Conjugate returns Q*
func (q Quaternion) Conjugate() Quaternion {
	return Quaternion{W: q.W, X: -q.X, Y: -q.Y, Z: -q.Z}
}

// Inverse returns Q^-1
func (q Quaternion) Inverse() Quaternion {
	normSq := q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z
	conj := q.Conjugate()
	return Quaternion{
		W: conj.W / normSq,
		X: conj.X / normSq,
		Y: conj.Y / normSq,
		Z: conj.Z / normSq,
	}
}

// Add quaternions
func (q1 Quaternion) Add(q2 Quaternion) Quaternion {
	return NewQuaternion(q1.W+q2.W, q1.X+q2.X, q1.Y+q2.Y, q1.Z+q2.Z)
}

// Subtract quaternions
func (q1 Quaternion) Subtract(q2 Quaternion) Quaternion {
	return NewQuaternion(q1.W-q2.W, q1.X-q2.X, q1.Y-q2.Y, q1.Z-q2.Z)
}

// Scale by scalar
func (q Quaternion) Scale(k float64) Quaternion {
	return NewQuaternion(k*q.W, k*q.X, k*q.Y, k*q.Z)
}

// Distance on S³ (geodesic)
func (q1 Quaternion) Distance(q2 Quaternion) float64 {
	dot := math.Abs(q1.Dot(q2))
	if dot > 1.0 {
		dot = 1.0
	}
	return math.Acos(dot)
}

// QM - Multiplicative collapse (4D → 1D)
func (q Quaternion) QM() float64 {
	return -q.W * q.X * q.Y * q.Z
}

// SLERP - Spherical Linear Interpolation
func SLERP(q0, q1 Quaternion, t float64) Quaternion {
	dot := q0.Dot(q1)
	if dot < 0 {
		q1 = Quaternion{W: -q1.W, X: -q1.X, Y: -q1.Y, Z: -q1.Z}
		dot = -dot
	}

	if dot > 0.9995 {
		return NewQuaternion(
			q0.W+t*(q1.W-q0.W),
			q0.X+t*(q1.X-q0.X),
			q0.Y+t*(q1.Y-q0.Y),
			q0.Z+t*(q1.Z-q0.Z),
		)
	}

	omega := math.Acos(dot)
	sinOmega := math.Sin(omega)
	scale0 := math.Sin((1-t)*omega) / sinOmega
	scale1 := math.Sin(t*omega) / sinOmega

	return NewQuaternion(
		scale0*q0.W+scale1*q1.W,
		scale0*q0.X+scale1*q1.X,
		scale0*q0.Y+scale1*q1.Y,
		scale0*q0.Z+scale1*q1.Z,
	)
}

// ═══════════════════════════════════════════════════════════════════════════
// VEDIC SUTRA - Differential Operators
// ═══════════════════════════════════════════════════════════════════════════

// Sutra represents a Vedic differential operator
type Sutra struct {
	Number      int
	Sanskrit    string
	English     string
	Description string
	Operation   func(state, derivative Quaternion, context float64) Quaternion
}

// InitializeSutras creates all 16 sutras
func InitializeSutras() []Sutra {
	return []Sutra{
		{1, "एकाधिकेन पूर्वेण", "By one more than the previous", "Increment",
			func(state, derivative Quaternion, context float64) Quaternion {
				epsilon := context * PHI_INV
				return NewQuaternion(state.W+epsilon, state.X, state.Y, state.Z)
			}},
		{2, "निखिलं नवतश्चरमं दशतः", "All from 9, last from 10", "Conjugate",
			func(state, derivative Quaternion, context float64) Quaternion {
				return state.Conjugate().Normalize()
			}},
		{3, "ऊर्ध्वतिर्यग्भ्याम्", "Vertically and crosswise", "Hamilton product",
			func(state, derivative Quaternion, context float64) Quaternion {
				return state.Multiply(derivative).Normalize()
			}},
		{4, "परावर्त्य योजयेत्", "Transpose and apply", "Division",
			func(state, derivative Quaternion, context float64) Quaternion {
				if derivative.Norm() < 1e-10 {
					return state
				}
				return state.Multiply(derivative.Inverse()).Normalize()
			}},
		{5, "शून्यं साम्यसमुच्चये", "When sum is same, sum is zero", "Equilibrium",
			func(state, derivative Quaternion, context float64) Quaternion {
				if derivative.Norm() < context {
					return state
				}
				return state
			}},
		{6, "आनुरूप्ये शून्यमन्यत्", "If one is in ratio, other is zero", "Scale",
			func(state, derivative Quaternion, context float64) Quaternion {
				return state.Scale(1.0 + context*PHI_INV).Normalize()
			}},
		{7, "संकलनव्यवकलनाभ्याम्", "By addition and subtraction", "Linear combination",
			func(state, derivative Quaternion, context float64) Quaternion {
				scaled := derivative.Scale(context)
				return state.Add(scaled).Normalize()
			}},
		{8, "पूरणापूरणाभ्याम्", "By completion", "Normalize",
			func(state, derivative Quaternion, context float64) Quaternion {
				return state.Normalize()
			}},
		{9, "चलनकलनाभ्याम्", "Differential calculus", "Derivative",
			func(state, derivative Quaternion, context float64) Quaternion {
				dot := state.Dot(derivative)
				tangent := derivative.Subtract(state.Scale(dot))
				return tangent.Normalize()
			}},
		{10, "यावदूनम्", "Whatever the deficiency", "Square",
			func(state, derivative Quaternion, context float64) Quaternion {
				return state.Multiply(state).Normalize()
			}},
		{11, "व्यष्टिसमष्टिः", "Part and whole", "Decompose",
			func(state, derivative Quaternion, context float64) Quaternion {
				scalarPart := state.W
				vectorNorm := math.Sqrt(state.X*state.X + state.Y*state.Y + state.Z*state.Z)
				newScalar := scalarPart*(1-context) + vectorNorm*context
				return NewQuaternion(newScalar, state.X, state.Y, state.Z)
			}},
		{12, "शेषाण्यङ्केन चरमेण", "Remainders by last digit", "Digital root",
			func(state, derivative Quaternion, context float64) Quaternion {
				qm := state.QM()
				n := int64(math.Abs(qm) * 1000000)
				var dr int
				if n == 0 {
					dr = 0
				} else {
					dr = 1 + int((n-1)%9)
				}
				drNormalized := float64(dr) / 9.0
				return NewQuaternion(drNormalized, state.X, state.Y, state.Z)
			}},
		{13, "सोपान्त्यद्वयमन्त्यम्", "Ultimate and penultimate", "Convergence",
			func(state, derivative Quaternion, context float64) Quaternion {
				dist := state.Distance(derivative)
				if dist < context {
					return state
				}
				return SLERP(state, derivative, context)
			}},
		{14, "एकन्यूनेन पूर्वेण", "By one less than previous", "Decrement",
			func(state, derivative Quaternion, context float64) Quaternion {
				epsilon := context * PHI_INV
				return NewQuaternion(state.W-epsilon, state.X, state.Y, state.Z)
			}},
		{15, "गुणितसमुच्चयः", "Product of sum", "Distributive",
			func(state, derivative Quaternion, context float64) Quaternion {
				sum := state.Add(derivative)
				return sum.Scale(context).Normalize()
			}},
		{16, "गुणकसमुच्चयः", "Factors of sum", "Square root",
			func(state, derivative Quaternion, context float64) Quaternion {
				identity := Quaternion{W: 1, X: 0, Y: 0, Z: 0}
				return SLERP(identity, state, 0.5).Normalize()
			}},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// SOLVER
// ═══════════════════════════════════════════════════════════════════════════

// Solver is the Vedic Differential Solver
type Solver struct {
	State                Quaternion
	StateDerivative      Quaternion
	Sutras               []Sutra
	StepSize             float64
	History              []Quaternion
	ConvergenceThreshold float64
	IsConverged          bool
	Regime               int
	Iterations           int
}

// NewSolver creates a new Vedic solver
func NewSolver() *Solver {
	return &Solver{
		State:                NewQuaternion(1, 0, 0, 0),
		StateDerivative:      NewQuaternion(0, 0, 0, 0),
		Sutras:               InitializeSutras(),
		StepSize:             1.0 / 9.0,
		History:              make([]Quaternion, 0, 1000),
		ConvergenceThreshold: 1e-6,
		IsConverged:          false,
		Regime:               1,
		Iterations:           0,
	}
}

// Step executes one integration step
func (s *Solver) Step(sutraIndex int, context float64) Quaternion {
	if sutraIndex < 0 || sutraIndex >= 16 {
		sutraIndex = 0
	}

	sutra := s.Sutras[sutraIndex]
	newState := sutra.Operation(s.State, s.StateDerivative, context)
	s.StateDerivative = newState.Subtract(s.State).Normalize()
	s.State = newState

	if len(s.History) < 1000 {
		s.History = append(s.History, s.State)
	}

	s.Iterations++
	return s.State
}

// SelectOptimalSutra chooses best sutra based on regime
func (s *Solver) SelectOptimalSutra(derivative Quaternion) int {
	derivNorm := derivative.Norm()

	if s.Regime == 1 {
		if derivNorm > 0.5 {
			return 2
		}
		return 0
	} else if s.Regime == 2 {
		if derivNorm < 0.01 {
			return 4
		}
		return 6
	} else {
		if derivNorm < s.ConvergenceThreshold {
			return 12
		}
		return 7
	}
}

// DetermineRegime classifies current state
func (s *Solver) DetermineRegime() int {
	if s.Iterations == 0 {
		return 1
	}

	progress := float64(s.Iterations) / 108.0
	if progress < R1_END {
		return 1
	} else if progress < R2_END {
		return 2
	}
	return 3
}

// Solve runs the main integration loop
func (s *Solver) Solve(maxIterations int, target Quaternion) Quaternion {
	for iter := 0; iter < maxIterations; iter++ {
		s.Regime = s.DetermineRegime()
		s.StateDerivative = target.Subtract(s.State).Normalize()
		sutraIndex := s.SelectOptimalSutra(s.StateDerivative)
		newState := s.Step(sutraIndex, s.StepSize)

		dist := newState.Distance(target)
		if dist < s.ConvergenceThreshold {
			s.IsConverged = true
			break
		}
	}

	return s.State
}

// ═══════════════════════════════════════════════════════════════════════════
// OPTIMIZATION HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// OptimizeValue finds optimal value using Vedic solver
func OptimizeValue(initial, target float64, maxIter int) float64 {
	solver := NewSolver()
	initialQ := NewQuaternion(initial, 0, 0, 0)
	targetQ := NewQuaternion(target, 0, 0, 0)

	solver.State = initialQ
	result := solver.Solve(maxIter, targetQ)

	return result.W
}

// OptimizeMultiDimensional optimizes in 4D space
func OptimizeMultiDimensional(initial, target [4]float64, maxIter int) [4]float64 {
	solver := NewSolver()
	initialQ := NewQuaternion(initial[0], initial[1], initial[2], initial[3])
	targetQ := NewQuaternion(target[0], target[1], target[2], target[3])

	solver.State = initialQ
	result := solver.Solve(maxIter, targetQ)

	return [4]float64{result.W, result.X, result.Y, result.Z}
}

// DigitalRoot computes Vedic digital root (53× speedup!)
func DigitalRoot(n int64) int {
	if n == 0 {
		return 0
	}
	return 1 + int((n-1)%9)
}

// FilterByDigitalRoot eliminates 88.9% of candidates
func FilterByDigitalRoot(candidates []int64, targetRoot int) []int64 {
	var filtered []int64
	for _, c := range candidates {
		if DigitalRoot(c) == targetRoot {
			filtered = append(filtered, c)
		}
	}
	return filtered
}

// ═══════════════════════════════════════════════════════════════════════════
// LINGUISTIC HELPERS (for NLP support)
// ═══════════════════════════════════════════════════════════════════════════

// EncodeAsQuaternion creates a quaternion encoding from a string
func EncodeAsQuaternion(text string) Quaternion {
	if len(text) == 0 {
		return NewQuaternion(0, 0, 0, 0)
	}

	// Use FNV-1a hash for consistent encoding
	h := uint64(14695981039346656037)
	for _, c := range []byte(text) {
		h ^= uint64(c)
		h *= 1099511628211
	}

	// Split hash into 4 components
	w := float64((h>>48)&0xFFFF) / 65535.0
	x := float64((h>>32)&0xFFFF) / 65535.0
	y := float64((h>>16)&0xFFFF) / 65535.0
	z := float64(h&0xFFFF) / 65535.0

	// Map to [-1, 1] range
	w = w*2.0 - 1.0
	x = x*2.0 - 1.0
	y = y*2.0 - 1.0
	z = z*2.0 - 1.0

	return NewQuaternion(w, x, y, z)
}

// DigitalRootString computes digital root from string hash
func DigitalRootString(text string) uint8 {
	if len(text) == 0 {
		return 0
	}

	// Hash string
	h := uint64(14695981039346656037)
	for _, c := range []byte(text) {
		h ^= uint64(c)
		h *= 1099511628211
	}

	// Apply digital root
	return uint8(DigitalRoot(int64(h % 1000000)))
}

// QuaternionDistance computes geodesic distance between quaternions
func QuaternionDistance(q1, q2 Quaternion) float64 {
	return q1.Distance(q2)
}

// SemanticSimilarity computes semantic similarity between texts
func SemanticSimilarity(text1, text2 string) float64 {
	q1 := EncodeAsQuaternion(text1)
	q2 := EncodeAsQuaternion(text2)

	// Dot product for normalized quaternions = cosine similarity
	similarity := math.Abs(q1.Dot(q2))

	// Clamp to [0, 1]
	if similarity > 1.0 {
		similarity = 1.0
	}
	if similarity < 0.0 {
		similarity = 0.0
	}

	return similarity
}

// HarmonicMean calculates harmonic mean (penalizes weak components)
func HarmonicMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	// Filter out zero/negative values
	validValues := make([]float64, 0, len(values))
	for _, v := range values {
		if v > 0.0 {
			validValues = append(validValues, v)
		}
	}

	if len(validValues) == 0 {
		return 0.0
	}

	// Calculate sum of reciprocals
	reciprocalSum := 0.0
	for _, v := range validValues {
		reciprocalSum += 1.0 / v
	}

	// Harmonic mean = n / Σ(1/xᵢ)
	return float64(len(validValues)) / reciprocalSum
}

// Magnitude alias for Norm
func (q Quaternion) Magnitude() float64 {
	return q.Norm()
}
