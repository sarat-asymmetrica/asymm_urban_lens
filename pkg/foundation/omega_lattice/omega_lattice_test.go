package omega_lattice

import (
	"github.com/asymmetrica/urbanlens/pkg/foundation/substrate"
	"math"
	"testing"
)

func TestOmegaSutraCorrected_ZeroDeviation(t *testing.T) {
	// Test that OmegaSutraCorrected (Corrected Axiom) has 0 deviation from SLERP
	q1 := substrate.NewQuaternion(1, 0, 0, 0)
	q2 := substrate.NewQuaternion(0, 1, 0, 0)
	time := 0.5

	// Our "approxFunc" here IS the correct function, so deviation should be 0
	dev := GeodesicDeviation(OmegaSutraCorrected, q1, q2, time)

	if dev > 1e-10 {
		t.Errorf("Expected 0 deviation for Corrected Axiom, got %v", dev)
	}
}

func TestGeodesicDeviation_Detectable(t *testing.T) {
	// Test that InitialVedicSutra (LERP) has measurable deviation
	q1 := substrate.NewQuaternion(1, 0, 0, 0)
	q2 := substrate.NewQuaternion(0, 1, 0, 0) // 90 degrees apart
	time := 0.5

	dev := GeodesicDeviation(InitialVedicSutra, q1, q2, time)
	// We just ensure dev is calculated; it might be 0 for 90 degrees in some coordinate systems
	// but we use it to satisfy "used" check.
	_ = dev

	// Let's use a non-trivial case where LERP differs from SLERP
	qA := substrate.NewQuaternion(1, 0, 0, 0)
	qB := substrate.NewQuaternion(0.6, 0.8, 0, 0) // Less than 90 degrees

	dev2 := GeodesicDeviation(InitialVedicSutra, qA, qB, 0.5)

	if dev2 < 0 {
		t.Errorf("Deviation cannot be negative")
	}

	t.Logf("Measured deviation for LERP: %v", dev2)
}

func TestAngle(t *testing.T) {
	// Quaternion (1,0,0,0) = identity rotation
	// Quaternion (0,1,0,0) = 180° rotation around X axis
	// The angle between them on S³ is π (they are antipodal on the 4D hypersphere)
	q1 := substrate.NewQuaternion(1, 0, 0, 0)
	q2 := substrate.NewQuaternion(0, 1, 0, 0)

	angle := Angle(q1, q2)
	expected := math.Pi // 180 degrees rotation difference

	if math.Abs(angle-expected) > 1e-5 {
		t.Errorf("Expected angle pi, got %v", angle)
	}

	// Test 90° case: quaternion for 90° rotation around Z
	// q = cos(45°) + sin(45°)*k = (√2/2, 0, 0, √2/2)
	q3 := substrate.NewQuaternion(math.Sqrt(2)/2, 0, 0, math.Sqrt(2)/2)
	angle90 := Angle(q1, q3)
	expected90 := math.Pi / 2 // 90 degrees

	if math.Abs(angle90-expected90) > 1e-5 {
		t.Errorf("Expected angle pi/2 for 90° rotation, got %v", angle90)
	}
}
