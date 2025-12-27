package omega_lattice

import (
	"github.com/asymmetrica/urbanlens/pkg/foundation/substrate"
	"math"
)

// OmegaSutraCorrected implements the zero-deviation corrected axiom for S³ interpolation.
// It aligns perfectly with the SLERP midpoint, ensuring geodesic precision.
//
// Formula: Ω_Sutr-Corrected(q1, q2, t) = SLERP(q1, q2, t)
func OmegaSutraCorrected(q1, q2 substrate.Quaternion, t float64) substrate.Quaternion {
	// The Corrected Axiom is mathematically equivalent to SLERP for the S3 manifold,
	// correcting the deviation found in the initial Vedic derivation.
	return substrate.SLERP(q1, q2, t)
}

// GeodesicDeviation calculates the error magnitude of an approximation function compared to the exact OmegaSutraCorrected.
// It returns the Euclidean distance ||q_exact - q_approx||.
func GeodesicDeviation(
	approxFunc func(substrate.Quaternion, substrate.Quaternion, float64) substrate.Quaternion,
	q1, q2 substrate.Quaternion,
	t float64,
) float64 {
	exactQ := OmegaSutraCorrected(q1, q2, t)
	approxQ := approxFunc(q1, q2, t)

	// Calculate Euclidean distance between the two quaternions
	diff := exactQ.Add(approxQ.Scale(-1.0))
	return diff.Norm()
}

// InitialVedicSutra approximates the midpoint (t=0.5) using the "Initial Derivation".
// Q' = [1 - Q.W, -Q.X, -Q.Y, -Q.Z]
// Note: This function serves as a historical reference to the deviation Ω_Dev.
// It assumes a specific context (e.g., deviation from identity or specific reflection).
// For general interpolation, we might use a linear approximation (LERP) to show deviation.
func InitialVedicSutra(q1, q2 substrate.Quaternion, t float64) substrate.Quaternion {
	// LERP (Linear Interpolation) followed by normalization is a common approximation
	// which deviates from the geodesic (SLERP).
	res := q1.Scale(1-t).Add(q2.Scale(t))
	return res.Normalize()
}

// Angle calculates the angle between two quaternions in radians.
// Used for analyzing geodesic properties.
func Angle(q1, q2 substrate.Quaternion) float64 {
	dot := q1.Dot(q2)
	// Clamp dot to [-1, 1] to avoid NaN
	if dot > 1.0 {
		dot = 1.0
	} else if dot < -1.0 {
		dot = -1.0
	}
	return 2 * math.Acos(math.Abs(dot))
}
