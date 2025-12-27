package lean

import (
	"math"
	"testing"

	mathpkg "github.com/asymmetrica/urbanlens/pkg/math"
)

// ============================================================================
// THEOREM 1 TESTS: Unit Quaternion Invariant
// ============================================================================

func TestIsUnit_Identity(t *testing.T) {
	// Lean: theorem one_isUnit : isUnit Quat.one
	identity := mathpkg.NewQuaternion(1, 0, 0, 0)
	if !IsUnit(identity) {
		t.Errorf("Identity quaternion (1,0,0,0) should be unit, got norm=%.15f", identity.Norm())
	}
}

func TestIsUnit_ImaginaryUnits(t *testing.T) {
	// Lean: theorem i_isUnit, j_isUnit, k_isUnit
	tests := []struct {
		name string
		q    mathpkg.Quaternion
	}{
		{"i", mathpkg.NewQuaternion(0, 1, 0, 0)},
		{"j", mathpkg.NewQuaternion(0, 0, 1, 0)},
		{"k", mathpkg.NewQuaternion(0, 0, 0, 1)},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if !IsUnit(tt.q) {
				t.Errorf("Imaginary unit %s should be unit, got norm=%.15f", tt.name, tt.q.Norm())
			}
		})
	}
}

func TestIsUnit_AfterNormalize(t *testing.T) {
	// Arbitrary quaternions become unit after normalization
	testCases := []mathpkg.Quaternion{
		mathpkg.NewQuaternion(1, 2, 3, 4),
		mathpkg.NewQuaternion(0.5, 0.5, 0.5, 0.5),
		mathpkg.NewQuaternion(100, -50, 75, -25),
	}

	for _, q := range testCases {
		qNorm := q.Normalize()
		if !IsUnit(qNorm) {
			t.Errorf("Normalized quaternion should be unit, got norm=%.15f for input (%v)", qNorm.Norm(), q)
		}
	}
}

func TestAssertUnit_Panic(t *testing.T) {
	// Non-unit quaternion should panic
	nonUnit := mathpkg.NewQuaternion(1, 2, 3, 4) // norm = √30 ≈ 5.477

	defer func() {
		if r := recover(); r == nil {
			t.Errorf("AssertUnit should panic on non-unit quaternion")
		}
	}()

	AssertUnit(nonUnit, "test context")
}

func TestAssertUnit_NoPanic(t *testing.T) {
	// Unit quaternion should not panic
	unit := mathpkg.NewQuaternion(1, 0, 0, 0)

	defer func() {
		if r := recover(); r != nil {
			t.Errorf("AssertUnit should not panic on unit quaternion: %v", r)
		}
	}()

	AssertUnit(unit, "test context")
}

// ============================================================================
// THEOREM 5 TESTS: SLERP Endpoints
// ============================================================================

func TestSLERP_Endpoints(t *testing.T) {
	// Lean: theorem slerp_zero, slerp_one
	q0 := mathpkg.NewQuaternion(1, 0, 0, 0).Normalize()
	q1 := mathpkg.NewQuaternion(0, 1, 0, 0).Normalize()

	// Test t=0 returns q0
	result0 := mathpkg.SLERP(q0, q1, 0.0)
	dist0 := quaternionDistance(result0, q0)
	if dist0 > SlerpTolerance {
		t.Errorf("SLERP(q0, q1, 0) should equal q0, distance=%.2e", dist0)
	}

	// Test t=1 returns q1
	result1 := mathpkg.SLERP(q0, q1, 1.0)
	dist1 := quaternionDistance(result1, q1)
	if dist1 > SlerpTolerance {
		t.Errorf("SLERP(q0, q1, 1) should equal q1, distance=%.2e", dist1)
	}
}

func TestSLERP_EndpointVariations(t *testing.T) {
	tests := []struct {
		name string
		q0   mathpkg.Quaternion
		q1   mathpkg.Quaternion
	}{
		{
			"orthogonal",
			mathpkg.NewQuaternion(1, 0, 0, 0),
			mathpkg.NewQuaternion(0, 1, 0, 0),
		},
		{
			"arbitrary",
			mathpkg.NewQuaternion(0.5, 0.5, 0.5, 0.5),
			mathpkg.NewQuaternion(0.8, 0.1, 0.3, 0.5).Normalize(),
		},
		{
			"near-parallel",
			mathpkg.NewQuaternion(1, 0, 0, 0),
			mathpkg.NewQuaternion(0.9999, 0.01, 0.01, 0.01).Normalize(),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			q0 := tt.q0.Normalize()
			q1 := tt.q1.Normalize()

			// No panic expected
			defer func() {
				if r := recover(); r != nil {
					t.Errorf("AssertSlerpEndpoints panicked: %v", r)
				}
			}()

			AssertSlerpEndpoints(q0, q1, "TestSLERP_EndpointVariations/"+tt.name)
		})
	}
}

// ============================================================================
// THEOREM 6 TESTS: SLERP Preserves S³
// ============================================================================

func TestSLERP_PreservesS3(t *testing.T) {
	// Lean: SLERP traces geodesic on S³, stays on unit sphere
	q0 := mathpkg.NewQuaternion(1, 0, 0, 0).Normalize()
	q1 := mathpkg.NewQuaternion(0, 1, 0, 0).Normalize()

	numSamples := 20
	for i := 0; i <= numSamples; i++ {
		tParam := float64(i) / float64(numSamples)
		qt := mathpkg.SLERP(q0, q1, tParam)

		if !IsUnit(qt) {
			norm := qt.Norm()
			t.Errorf("SLERP(q0, q1, %.3f) should be unit, got norm=%.15f (Δ=%.2e)", tParam, norm, math.Abs(norm-1.0))
		}
	}
}

func TestSLERP_PreservesS3_Variations(t *testing.T) {
	tests := []struct {
		name string
		q0   mathpkg.Quaternion
		q1   mathpkg.Quaternion
	}{
		{
			"identity-to-i",
			mathpkg.NewQuaternion(1, 0, 0, 0),
			mathpkg.NewQuaternion(0, 1, 0, 0),
		},
		{
			"i-to-j",
			mathpkg.NewQuaternion(0, 1, 0, 0),
			mathpkg.NewQuaternion(0, 0, 1, 0),
		},
		{
			"arbitrary",
			mathpkg.NewQuaternion(0.6, 0.8, 0, 0).Normalize(),
			mathpkg.NewQuaternion(0.2, 0.3, 0.7, 0.6).Normalize(),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			q0 := tt.q0.Normalize()
			q1 := tt.q1.Normalize()

			// No panic expected
			defer func() {
				if r := recover(); r != nil {
					t.Errorf("AssertSlerpPreservesS3 panicked: %v", r)
				}
			}()

			AssertSlerpPreservesS3(q0, q1, 20, "TestSLERP_PreservesS3_Variations/"+tt.name)
		})
	}
}

// ============================================================================
// THEOREM 7-8 TESTS: Three-Regime Dynamics
// ============================================================================

func TestThreeRegime_TypicalRegime(t *testing.T) {
	// Lean: theorem typical_is_stable
	typical := TypicalRegime()

	// Check sum to unity
	sum := typical.R1 + typical.R2 + typical.R3
	if math.Abs(sum-1.0) > 1e-9 {
		t.Errorf("Typical regime should sum to 1.0, got %.15f", sum)
	}

	// Check stability
	if !typical.IsStable() {
		t.Errorf("Typical regime should be stable (R3=%.2f >= 0.5)", typical.R3)
	}

	// Check not danger
	if typical.IsDanger() {
		t.Errorf("Typical regime should not be in danger (R2=%.2f >= 0.15)", typical.R2)
	}
}

func TestAssertThreeRegime_Valid(t *testing.T) {
	// Valid regime should not panic
	valid := NewThreeRegime(0.30, 0.20, 0.50)

	defer func() {
		if r := recover(); r != nil {
			t.Errorf("AssertThreeRegime should not panic on valid regime: %v", r)
		}
	}()

	AssertThreeRegime(valid, "test valid regime")
}

func TestAssertThreeRegime_InvalidSum(t *testing.T) {
	// Sum != 1.0 should panic
	invalid := NewThreeRegime(0.30, 0.30, 0.30) // Sum = 0.90

	defer func() {
		if r := recover(); r == nil {
			t.Errorf("AssertThreeRegime should panic when sum != 1.0")
		}
	}()

	AssertThreeRegime(invalid, "test invalid sum")
}

func TestAssertThreeRegime_NegativeRegime(t *testing.T) {
	// Negative regime should panic
	invalid := NewThreeRegime(-0.10, 0.60, 0.50)

	defer func() {
		if r := recover(); r == nil {
			t.Errorf("AssertThreeRegime should panic on negative regime")
		}
	}()

	AssertThreeRegime(invalid, "test negative regime")
}

func TestAssertThreeRegime_ExceedsOne(t *testing.T) {
	// R > 1.0 should panic (even if sum = 1.0 is impossible)
	invalid := NewThreeRegime(0.80, 0.70, -0.50)

	defer func() {
		if r := recover(); r == nil {
			t.Errorf("AssertThreeRegime should panic when any regime exceeds 1.0")
		}
	}()

	AssertThreeRegime(invalid, "test exceeds one")
}

// ============================================================================
// THEOREM 9 TESTS: Stability Criterion
// ============================================================================

func TestThreeRegime_StabilityCriterion(t *testing.T) {
	tests := []struct {
		name     string
		regime   ThreeRegime
		isStable bool
	}{
		{"stable (R3=0.50)", NewThreeRegime(0.30, 0.20, 0.50), true},
		{"stable (R3=0.60)", NewThreeRegime(0.25, 0.15, 0.60), true},
		{"unstable (R3=0.49)", NewThreeRegime(0.31, 0.20, 0.49), false},
		{"unstable (R3=0.30)", NewThreeRegime(0.40, 0.30, 0.30), false},
		{"danger (R2=0.14)", NewThreeRegime(0.46, 0.14, 0.40), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if tt.regime.IsStable() != tt.isStable {
				t.Errorf("IsStable() = %v, want %v for regime (R1=%.2f, R2=%.2f, R3=%.2f)",
					tt.regime.IsStable(), tt.isStable, tt.regime.R1, tt.regime.R2, tt.regime.R3)
			}
		})
	}
}

func TestThreeRegime_DangerZone(t *testing.T) {
	tests := []struct {
		name     string
		regime   ThreeRegime
		isDanger bool
	}{
		{"safe (R2=0.20)", NewThreeRegime(0.30, 0.20, 0.50), false},
		{"safe (R2=0.15)", NewThreeRegime(0.35, 0.15, 0.50), false},
		{"danger (R2=0.14)", NewThreeRegime(0.36, 0.14, 0.50), true},
		{"danger (R2=0.10)", NewThreeRegime(0.40, 0.10, 0.50), true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if tt.regime.IsDanger() != tt.isDanger {
				t.Errorf("IsDanger() = %v, want %v for regime (R1=%.2f, R2=%.2f, R3=%.2f)",
					tt.regime.IsDanger(), tt.isDanger, tt.regime.R1, tt.regime.R2, tt.regime.R3)
			}
		})
	}
}

// ============================================================================
// METADATA TESTS
// ============================================================================

func TestS3Theorems_Metadata(t *testing.T) {
	theorems := S3Theorems()

	if len(theorems) == 0 {
		t.Errorf("S3Theorems() should return non-empty list")
	}

	for i, thm := range theorems {
		if thm.TheoremName == "" {
			t.Errorf("Theorem %d has empty name", i)
		}
		if thm.LeanFile == "" {
			t.Errorf("Theorem %d (%s) has empty Lean file", i, thm.TheoremName)
		}
		if thm.LineNumber == 0 {
			t.Errorf("Theorem %d (%s) has zero line number", i, thm.TheoremName)
		}
		if thm.ProofStatus != "Proven" && thm.ProofStatus != "Axiomatized" {
			t.Errorf("Theorem %d (%s) has invalid proof status: %s", i, thm.TheoremName, thm.ProofStatus)
		}
	}
}

func TestConstants(t *testing.T) {
	// Verify mathematical constants
	if ThermodynamicAttractor != 0.87532 {
		t.Errorf("ThermodynamicAttractor should be 0.87532, got %.5f", ThermodynamicAttractor)
	}

	if math.Abs(SevenEighths-7.0/8.0) > 1e-15 {
		t.Errorf("SevenEighths should be 7/8, got %.15f", SevenEighths)
	}

	if math.Abs(GoldenRatio-1.618033988749895) > 1e-15 {
		t.Errorf("GoldenRatio should be (1+√5)/2, got %.15f", GoldenRatio)
	}

	// Verify attractor near 7/8
	diff := math.Abs(ThermodynamicAttractor - SevenEighths)
	if diff >= 0.005 {
		t.Errorf("ThermodynamicAttractor should be within 0.5%% of 7/8, diff=%.4f", diff)
	}
}

// ============================================================================
// BENCHMARK: Verify Runtime Assertions Don't Kill Performance
// ============================================================================

func BenchmarkIsUnit(b *testing.B) {
	q := mathpkg.NewQuaternion(1, 0, 0, 0)
	for i := 0; i < b.N; i++ {
		IsUnit(q)
	}
}

func BenchmarkAssertUnit(b *testing.B) {
	q := mathpkg.NewQuaternion(1, 0, 0, 0)
	for i := 0; i < b.N; i++ {
		AssertUnit(q, "benchmark")
	}
}

func BenchmarkSLERP(b *testing.B) {
	q0 := mathpkg.NewQuaternion(1, 0, 0, 0).Normalize()
	q1 := mathpkg.NewQuaternion(0, 1, 0, 0).Normalize()
	for i := 0; i < b.N; i++ {
		mathpkg.SLERP(q0, q1, 0.5)
	}
}

func BenchmarkAssertSlerpEndpoints(b *testing.B) {
	q0 := mathpkg.NewQuaternion(1, 0, 0, 0).Normalize()
	q1 := mathpkg.NewQuaternion(0, 1, 0, 0).Normalize()
	for i := 0; i < b.N; i++ {
		AssertSlerpEndpoints(q0, q1, "benchmark")
	}
}
