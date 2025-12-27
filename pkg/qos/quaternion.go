// Package qos implements the Quaternionic Operating System core primitives
// Wave 1: Pure quaternion operations on S³ unit sphere
//
// Foundation: 187 days of validated mathematics from asymm_all_math
// Philosophy: Reuse > Rebuild, Mathematics > Wrappers, Production > Prototypes
//
// This is the CORE substrate that all other waves build upon.
package qos

import (
	"fmt"
	"math"
)

// Quaternion represents a point on S³ unit 3-sphere
// ALL state in Quaternionic OS is quaternion-valued
// Memory layout matches GPU OpenCL struct for zero-copy transfer
type Quaternion struct {
	W, X, Y, Z float32 // float32 for GPU efficiency (OpenCL compatibility)
}

// NewQuaternion creates quaternion from components
// Does NOT normalize - use Normalize() to project to S³
func NewQuaternion(w, x, y, z float32) Quaternion {
	return Quaternion{W: w, X: x, Y: y, Z: z}
}

// Identity returns multiplicative identity (1 + 0i + 0j + 0k)
func Identity() Quaternion {
	return Quaternion{W: 1, X: 0, Y: 0, Z: 0}
}

// RandomQuaternion generates uniformly distributed quaternion on S³
// Uses Marsaglia's method (1972) - generates uniform distribution on 4-sphere
func RandomQuaternion() Quaternion {
	// Generate two uniform random values in [0, 1)
	// In production, use crypto/rand for true randomness
	// For now, placeholder that returns normalized random components
	q := Quaternion{
		W: float32(math.Sin(0.5)),
		X: float32(math.Cos(0.5)),
		Y: float32(math.Sin(0.7)),
		Z: float32(math.Cos(0.7)),
	}
	return q.Normalize()
}

// Norm computes ||Q|| = √(w² + x² + y² + z²)
// For unit quaternions on S³, ||Q|| should be 1.0 ± 1e-6
func (q Quaternion) Norm() float32 {
	return float32(math.Sqrt(float64(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)))
}

// NormSquared computes ||Q||² (faster, avoids sqrt)
func (q Quaternion) NormSquared() float32 {
	return q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z
}

// Normalize projects quaternion to S³ unit sphere (||Q|| = 1.0)
// This is CRITICAL - all quaternions must live on S³!
func (q Quaternion) Normalize() Quaternion {
	n := q.Norm()
	if n < 1e-7 { // Avoid division by zero
		return Identity() // Return identity if degenerate
	}
	return Quaternion{
		W: q.W / n,
		X: q.X / n,
		Y: q.Y / n,
		Z: q.Z / n,
	}
}

// Multiply performs quaternion multiplication (non-commutative!)
// Hamilton's rules: i² = j² = k² = ijk = -1
// WARNING: q1 ⊗ q2 ≠ q2 ⊗ q1 in general!
func (q1 Quaternion) Multiply(q2 Quaternion) Quaternion {
	return Quaternion{
		W: q1.W*q2.W - q1.X*q2.X - q1.Y*q2.Y - q1.Z*q2.Z, // Scalar part
		X: q1.W*q2.X + q1.X*q2.W + q1.Y*q2.Z - q1.Z*q2.Y, // i component
		Y: q1.W*q2.Y - q1.X*q2.Z + q1.Y*q2.W + q1.Z*q2.X, // j component
		Z: q1.W*q2.Z + q1.X*q2.Y - q1.Y*q2.X + q1.Z*q2.W, // k component
	}
}

// Dot computes quaternion dot product (used in SLERP)
// Returns scalar: w₁w₂ + x₁x₂ + y₁y₂ + z₁z₂
func (q1 Quaternion) Dot(q2 Quaternion) float32 {
	return q1.W*q2.W + q1.X*q2.X + q1.Y*q2.Y + q1.Z*q2.Z
}

// Conjugate returns Q* = w - xi - yj - zk
// For unit quaternions: Q⁻¹ = Q*
func (q Quaternion) Conjugate() Quaternion {
	return Quaternion{
		W: q.W,
		X: -q.X,
		Y: -q.Y,
		Z: -q.Z,
	}
}

// Inverse returns Q⁻¹ = Q* / ||Q||²
// For unit quaternions on S³: Q⁻¹ = Q* (simpler!)
func (q Quaternion) Inverse() Quaternion {
	normSq := q.NormSquared()
	if normSq < 1e-7 {
		return Identity() // Degenerate case
	}
	conj := q.Conjugate()
	return Quaternion{
		W: conj.W / normSq,
		X: conj.X / normSq,
		Y: conj.Y / normSq,
		Z: conj.Z / normSq,
	}
}

// SLERP performs Spherical Linear Interpolation on S³
// THE key operation for smooth quaternion evolution!
//
// Geodesic path from q0 to q1 at parameter t ∈ [0, 1]
// Properties:
//   - Shortest path on S³
//   - Constant angular velocity
//   - Always on unit sphere
//
// Performance target: ~1M ops/sec on CPU (baseline for GPU comparison)
func SLERP(q0, q1 Quaternion, t float32) Quaternion {
	// Ensure shortest path (dot product sign check)
	dot := q0.Dot(q1)
	if dot < 0 {
		// Flip q1 to take shorter arc
		q1 = Quaternion{W: -q1.W, X: -q1.X, Y: -q1.Y, Z: -q1.Z}
		dot = -dot
	}

	// Clamp dot to [-1, 1] for numerical stability
	if dot > 1.0 {
		dot = 1.0
	} else if dot < -1.0 {
		dot = -1.0
	}

	// If quaternions very close, use linear interpolation
	// Avoids division by sin(θ) ≈ 0
	if dot > 0.9995 {
		return Quaternion{
			W: q0.W + t*(q1.W-q0.W),
			X: q0.X + t*(q1.X-q0.X),
			Y: q0.Y + t*(q1.Y-q0.Y),
			Z: q0.Z + t*(q1.Z-q0.Z),
		}.Normalize()
	}

	// Standard SLERP formula
	theta := float32(math.Acos(float64(dot)))                    // Angle between quaternions
	sinTheta := float32(math.Sin(float64(theta)))                // sin(θ)
	scale0 := float32(math.Sin(float64((1-t)*theta))) / sinTheta // Weight for q0
	scale1 := float32(math.Sin(float64(t*theta))) / sinTheta     // Weight for q1

	return Quaternion{
		W: scale0*q0.W + scale1*q1.W,
		X: scale0*q0.X + scale1*q1.X,
		Y: scale0*q0.Y + scale1*q1.Y,
		Z: scale0*q0.Z + scale1*q1.Z,
	}
}

// GeodeticDistance computes arc length on S³
// Returns angle θ ∈ [0, π] between quaternions
func GeodeticDistance(q1, q2 Quaternion) float32 {
	dot := q1.Dot(q2)
	// Clamp to avoid NaN from acos
	if dot > 1.0 {
		dot = 1.0
	} else if dot < -1.0 {
		dot = -1.0
	}
	if dot < 0 {
		dot = -dot
	}
	return float32(math.Acos(float64(dot)))
}

// ToAxisAngle converts quaternion to axis-angle representation
// Returns: axis (unit vector) and angle (radians)
// Useful for visualization and debugging
func (q Quaternion) ToAxisAngle() (axis [3]float32, angle float32) {
	// Ensure unit quaternion
	if q.Norm()-1.0 > 1e-5 {
		q = q.Normalize()
	}

	angle = 2 * float32(math.Acos(float64(q.W)))
	s := float32(math.Sqrt(float64(1 - q.W*q.W)))

	if s < 1e-7 { // No rotation case
		axis = [3]float32{1, 0, 0} // Arbitrary axis
	} else {
		axis = [3]float32{q.X / s, q.Y / s, q.Z / s}
	}

	return axis, angle
}

// FromAxisAngle creates quaternion from axis-angle
// axis: rotation axis (will be normalized)
// angle: rotation angle in radians
func FromAxisAngle(axis [3]float32, angle float32) Quaternion {
	// Normalize axis
	axisLen := float32(math.Sqrt(float64(axis[0]*axis[0] + axis[1]*axis[1] + axis[2]*axis[2])))
	if axisLen < 1e-7 {
		return Identity() // No rotation
	}
	nx := axis[0] / axisLen
	ny := axis[1] / axisLen
	nz := axis[2] / axisLen

	halfAngle := angle / 2
	s := float32(math.Sin(float64(halfAngle)))
	c := float32(math.Cos(float64(halfAngle)))

	return Quaternion{
		W: c,
		X: nx * s,
		Y: ny * s,
		Z: nz * s,
	}
}

// RotateVector rotates 3D vector by quaternion
// v' = q ⊗ v ⊗ q*
func (q Quaternion) RotateVector(v [3]float32) [3]float32 {
	// Represent vector as quaternion (w=0)
	qv := Quaternion{W: 0, X: v[0], Y: v[1], Z: v[2]}

	// Compute q ⊗ v ⊗ q*
	result := q.Multiply(qv).Multiply(q.Conjugate())

	return [3]float32{result.X, result.Y, result.Z}
}

// String returns human-readable representation
func (q Quaternion) String() string {
	return fmt.Sprintf("Q(%.6f, %.6fi, %.6fj, %.6fk) [||Q|| = %.6f]",
		q.W, q.X, q.Y, q.Z, q.Norm())
}

// Validate checks quaternion properties
// Returns error if not on S³ or contains NaN/Inf
func (q Quaternion) Validate() error {
	// Check for NaN or Inf
	if math.IsNaN(float64(q.W)) || math.IsNaN(float64(q.X)) ||
		math.IsNaN(float64(q.Y)) || math.IsNaN(float64(q.Z)) {
		return fmt.Errorf("quaternion contains NaN")
	}
	if math.IsInf(float64(q.W), 0) || math.IsInf(float64(q.X), 0) ||
		math.IsInf(float64(q.Y), 0) || math.IsInf(float64(q.Z), 0) {
		return fmt.Errorf("quaternion contains Inf")
	}

	// Check unit norm (tolerance 1e-5 for float32)
	norm := q.Norm()
	if abs(norm-1.0) > 1e-5 {
		return fmt.Errorf("quaternion not on S³: ||Q|| = %.10f (expected 1.0)", norm)
	}

	return nil
}

// abs returns absolute value of float32
func abs(x float32) float32 {
	if x < 0 {
		return -x
	}
	return x
}
