package gpu

import (
	"math"
	"testing"
)

func TestQuaternionIdentity(t *testing.T) {
	q := Identity()
	if q.W != 1 || q.X != 0 || q.Y != 0 || q.Z != 0 {
		t.Errorf("Identity() = %v, want (1, 0, 0, 0)", q)
	}
}

func TestQuaternionNorm(t *testing.T) {
	q := NewQuaternion(1, 2, 3, 4)
	expected := float32(math.Sqrt(1 + 4 + 9 + 16))
	if abs(q.Norm()-expected) > 1e-5 {
		t.Errorf("Norm() = %v, want %v", q.Norm(), expected)
	}
}

func TestQuaternionNormalize(t *testing.T) {
	q := NewQuaternion(1, 2, 3, 4)
	n := q.Normalize()
	if abs(n.Norm()-1.0) > 1e-5 {
		t.Errorf("Normalized norm = %v, want 1.0", n.Norm())
	}
}

func TestQuaternionMultiply(t *testing.T) {
	q1 := Identity()
	q2 := NewQuaternion(0, 1, 0, 0).Normalize()

	result := q1.Multiply(q2)
	if abs(result.X-q2.X) > 1e-5 {
		t.Errorf("Identity * q2 should equal q2")
	}
}

func TestSLERP(t *testing.T) {
	q0 := Identity()
	q1 := FromAxisAngle([3]float32{0, 0, 1}, float32(math.Pi/2))

	// t=0 should give q0
	result0 := SLERP(q0, q1, 0)
	if abs(result0.W-q0.W) > 1e-4 {
		t.Errorf("SLERP(q0, q1, 0) should equal q0")
	}

	// t=1 should give q1
	result1 := SLERP(q0, q1, 1)
	if abs(result1.W-q1.W) > 1e-4 {
		t.Errorf("SLERP(q0, q1, 1) should equal q1")
	}

	// t=0.5 should be halfway
	result05 := SLERP(q0, q1, 0.5)
	if result05.Validate() != nil {
		t.Errorf("SLERP result should be on S³")
	}
}

func TestGeodeticDistance(t *testing.T) {
	q1 := Identity()
	q2 := Identity()

	dist := GeodeticDistance(q1, q2)
	if dist > 1e-5 {
		t.Errorf("Distance between identical quaternions should be 0, got %v", dist)
	}
}

func TestRotateVector(t *testing.T) {
	// 90 degree rotation around Z axis
	q := FromAxisAngle([3]float32{0, 0, 1}, float32(math.Pi/2))
	v := [3]float32{1, 0, 0}

	result := q.RotateVector(v)

	// X axis should become Y axis
	if abs(result[0]) > 0.01 || abs(result[1]-1) > 0.01 {
		t.Errorf("90° Z rotation of (1,0,0) should give (0,1,0), got %v", result)
	}
}

func TestValidate(t *testing.T) {
	// Valid unit quaternion
	q := Identity()
	if err := q.Validate(); err != nil {
		t.Errorf("Identity should be valid: %v", err)
	}

	// Non-unit quaternion
	q2 := NewQuaternion(2, 0, 0, 0)
	if err := q2.Validate(); err == nil {
		t.Error("Non-unit quaternion should fail validation")
	}
}

func BenchmarkSLERP(b *testing.B) {
	q0 := Identity()
	q1 := FromAxisAngle([3]float32{0, 0, 1}, float32(math.Pi/2))

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = SLERP(q0, q1, 0.5)
	}
}

func BenchmarkMultiply(b *testing.B) {
	q1 := RandomQuaternion()
	q2 := RandomQuaternion()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = q1.Multiply(q2)
	}
}
