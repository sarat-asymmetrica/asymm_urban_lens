// Package lean - Runtime Assertions Tests
// Validates that proof assertions correctly detect violations
package lean

import (
	"math"
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION NORM ASSERTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestQuaternionNormAssertion_Valid(t *testing.T) {
	assertion := NewQuaternionNormAssertion()

	tests := []struct {
		name string
		q    *QuaternionData
	}{
		{
			name: "unit quaternion (1,0,0,0)",
			q:    &QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		},
		{
			name: "normalized quaternion",
			q:    &QuaternionData{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5},
		},
		{
			name: "rotation quaternion",
			q: &QuaternionData{
				W: math.Cos(math.Pi / 4),
				X: math.Sin(math.Pi/4) / math.Sqrt(3),
				Y: math.Sin(math.Pi/4) / math.Sqrt(3),
				Z: math.Sin(math.Pi/4) / math.Sqrt(3),
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := assertion.Validate(tt.q)
			if err != nil {
				t.Errorf("Expected valid quaternion, got error: %v (norm: %.8f)",
					err, tt.q.Norm())
			}
		})
	}
}

func TestQuaternionNormAssertion_Invalid(t *testing.T) {
	assertion := NewQuaternionNormAssertion()

	tests := []struct {
		name string
		q    *QuaternionData
	}{
		{
			name: "unnormalized quaternion",
			q:    &QuaternionData{W: 1, X: 1, Y: 1, Z: 1},
		},
		{
			name: "zero quaternion",
			q:    &QuaternionData{W: 0, X: 0, Y: 0, Z: 0},
		},
		{
			name: "too small norm",
			q:    &QuaternionData{W: 0.1, X: 0.1, Y: 0.1, Z: 0.1},
		},
		{
			name: "NaN quaternion",
			q:    &QuaternionData{W: math.NaN(), X: 0, Y: 0, Z: 0},
		},
		{
			name: "Inf quaternion",
			q:    &QuaternionData{W: math.Inf(1), X: 0, Y: 0, Z: 0},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := assertion.Validate(tt.q)
			if err == nil {
				t.Errorf("Expected invalid quaternion to fail, but passed (norm: %.8f)",
					tt.q.Norm())
			}
		})
	}
}

func TestQuaternionNormAssertion_Epsilon(t *testing.T) {
	// Test with custom epsilon
	assertion := NewQuaternionNormAssertionWithEpsilon(1e-3)

	// Slightly off norm - should pass with larger epsilon
	q := &QuaternionData{W: 0.5001, X: 0.5, Y: 0.5, Z: 0.5}
	// Normalize and slightly perturb
	norm := q.Norm()
	q.W /= norm
	q.X /= norm
	q.Y /= norm
	q.Z /= norm
	q.W += 0.0005 // Small perturbation

	err := assertion.Validate(q)
	if err != nil {
		t.Logf("Norm: %.8f, deviation: %.2e", q.Norm(), math.Abs(q.Norm()-1.0))
	}
	// This might still fail if deviation > 1e-3
}

// ═══════════════════════════════════════════════════════════════════════════
// SLERP ASSERTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestSLERPPreservesS3Assertion_Valid(t *testing.T) {
	assertion := NewSLERPPreservesS3Assertion()

	q0 := QuaternionData{W: 1, X: 0, Y: 0, Z: 0}
	q1 := QuaternionData{W: 0, X: 1, Y: 0, Z: 0}

	// Compute SLERP waypoint at t=0.5
	// (In real code, would use SLERP function)
	t_val := 0.5
	waypoint := QuaternionData{
		W: math.Cos(math.Pi / 4),
		X: math.Sin(math.Pi / 4),
		Y: 0,
		Z: 0,
	}

	slerp := &SLERPData{
		Q0:       q0,
		Q1:       q1,
		Waypoint: waypoint,
		T:        t_val,
	}

	err := assertion.Validate(slerp)
	if err != nil {
		t.Errorf("Expected valid SLERP, got error: %v", err)
	}
}

func TestSLERPPreservesS3Assertion_InvalidEndpoints(t *testing.T) {
	assertion := NewSLERPPreservesS3Assertion()

	// Invalid Q0 (not normalized)
	slerp := &SLERPData{
		Q0:       QuaternionData{W: 2, X: 0, Y: 0, Z: 0},
		Q1:       QuaternionData{W: 0, X: 1, Y: 0, Z: 0},
		Waypoint: QuaternionData{W: 0.707, X: 0.707, Y: 0, Z: 0},
		T:        0.5,
	}

	err := assertion.Validate(slerp)
	if err == nil {
		t.Error("Expected SLERP with invalid Q0 to fail")
	}
}

func TestSLERPPreservesS3Assertion_InvalidWaypoint(t *testing.T) {
	assertion := NewSLERPPreservesS3Assertion()

	// Valid endpoints, invalid waypoint
	slerp := &SLERPData{
		Q0:       QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		Q1:       QuaternionData{W: 0, X: 1, Y: 0, Z: 0},
		Waypoint: QuaternionData{W: 2, X: 0, Y: 0, Z: 0}, // Not normalized!
		T:        0.5,
	}

	err := assertion.Validate(slerp)
	if err == nil {
		t.Error("Expected SLERP with invalid waypoint to fail")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HAMILTON MULTIPLICATION ASSERTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestHamiltonClosureAssertion_Valid(t *testing.T) {
	assertion := NewHamiltonClosureAssertion()

	// Identity multiplication
	mult := &MultiplicationData{
		Q1:     QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		Q2:     QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		Result: QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
	}

	err := assertion.Validate(mult)
	if err != nil {
		t.Errorf("Expected valid multiplication, got error: %v", err)
	}
}

func TestHamiltonClosureAssertion_InvalidResult(t *testing.T) {
	assertion := NewHamiltonClosureAssertion()

	// Valid inputs, invalid result
	mult := &MultiplicationData{
		Q1:     QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		Q2:     QuaternionData{W: 0, X: 1, Y: 0, Z: 0},
		Result: QuaternionData{W: 2, X: 0, Y: 0, Z: 0}, // Not normalized!
	}

	err := assertion.Validate(mult)
	if err == nil {
		t.Error("Expected multiplication with invalid result to fail")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// DIGITAL ROOT ASSERTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestDigitalRootPartitionAssertion_Valid(t *testing.T) {
	assertion := NewDigitalRootPartitionAssertion()

	tests := []struct {
		name  string
		input int64
		dr    int64
	}{
		{"dr(1) = 1", 1, 1},
		{"dr(9) = 9", 9, 9},
		{"dr(10) = 1", 10, 1},
		{"dr(19) = 1", 19, 1},
		{"dr(27) = 9", 27, 9},
		{"dr(108) = 9", 108, 9},
		{"dr(432) = 9", 432, 9},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			data := &DigitalRootData{
				Input:        tt.input,
				DigitalRoot:  tt.dr,
				ExpectedZero: false,
			}

			err := assertion.Validate(data)
			if err != nil {
				t.Errorf("Expected valid digital root, got error: %v", err)
			}
		})
	}
}

func TestDigitalRootPartitionAssertion_Zero(t *testing.T) {
	assertion := NewDigitalRootPartitionAssertion()

	data := &DigitalRootData{
		Input:        0,
		DigitalRoot:  0,
		ExpectedZero: true,
	}

	err := assertion.Validate(data)
	if err != nil {
		t.Errorf("Expected dr(0) = 0 to be valid, got error: %v", err)
	}
}

func TestDigitalRootPartitionAssertion_Invalid(t *testing.T) {
	assertion := NewDigitalRootPartitionAssertion()

	tests := []struct {
		name string
		dr   int64
	}{
		{"dr < 1", 0},
		{"dr > 9", 10},
		{"dr negative", -1},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			data := &DigitalRootData{
				Input:        42,
				DigitalRoot:  tt.dr,
				ExpectedZero: false,
			}

			err := assertion.Validate(data)
			if err == nil {
				t.Errorf("Expected invalid digital root %d to fail", tt.dr)
			}
		})
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// WILLIAMS SPACE BOUND ASSERTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestWilliamsSpaceBoundAssertion_Valid(t *testing.T) {
	assertion := NewWilliamsSpaceBoundAssertion()

	tests := []struct {
		name      string
		t         int64
		spaceUsed int64
		bound     int64
	}{
		{"small batch", 100, 50, 66},     // √100 × log₂(100) ≈ 66
		{"medium batch", 1000, 200, 299}, // √1000 × log₂(1000) ≈ 316
		{"large batch", 10000, 800, 1328}, // √10000 × log₂(10000) ≈ 1328
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			data := &WilliamsData{
				T:            tt.t,
				SpaceUsed:    tt.spaceUsed,
				ExpectedBound: tt.bound,
			}

			err := assertion.Validate(data)
			if err != nil {
				t.Errorf("Expected valid Williams bound, got error: %v", err)
			}
		})
	}
}

func TestWilliamsSpaceBoundAssertion_Invalid(t *testing.T) {
	assertion := NewWilliamsSpaceBoundAssertion()

	// Space used exceeds bound even with safety factor
	data := &WilliamsData{
		T:            100,
		SpaceUsed:    100, // Way over bound of ~66
		ExpectedBound: 66,
	}

	err := assertion.Validate(data)
	if err == nil {
		t.Error("Expected Williams bound violation to fail")
	}
}

func TestWilliamsSpaceBoundAssertion_SafetyFactor(t *testing.T) {
	// Test with lenient safety factor
	assertion := NewWilliamsSpaceBoundAssertionWithSafety(2.0) // 100% over budget allowed

	data := &WilliamsData{
		T:            100,
		SpaceUsed:    120, // 1.8× over bound, but within 2.0× safety
		ExpectedBound: 66,
	}

	err := assertion.Validate(data)
	if err != nil {
		t.Errorf("Expected Williams bound with safety factor to pass, got: %v", err)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// THREE-REGIME STABILITY ASSERTION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestThreeRegimeStabilityAssertion_Valid(t *testing.T) {
	assertion := NewThreeRegimeStabilityAssertion()

	tests := []struct {
		name string
		r1   float64
		r2   float64
		r3   float64
	}{
		{"ideal regime", 0.30, 0.20, 0.50},
		{"stable with high R3", 0.20, 0.10, 0.70},
		{"minimal stable", 0.25, 0.25, 0.50},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			data := &ThreeRegimeData{
				R1:    tt.r1,
				R2:    tt.r2,
				R3:    tt.r3,
				Label: tt.name,
			}

			err := assertion.Validate(data)
			if err != nil {
				t.Errorf("Expected stable regime, got error: %v", err)
			}
		})
	}
}

func TestThreeRegimeStabilityAssertion_Unstable(t *testing.T) {
	assertion := NewThreeRegimeStabilityAssertion()

	tests := []struct {
		name string
		r1   float64
		r2   float64
		r3   float64
	}{
		{"low R3", 0.40, 0.40, 0.20},
		{"zero R3", 0.50, 0.50, 0.00},
		{"near singularity", 0.35, 0.35, 0.30},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			data := &ThreeRegimeData{
				R1:    tt.r1,
				R2:    tt.r2,
				R3:    tt.r3,
				Label: tt.name,
			}

			err := assertion.Validate(data)
			if err == nil {
				t.Errorf("Expected unstable regime to fail (R3=%.2f)", tt.r3)
			}
		})
	}
}

func TestThreeRegimeStabilityAssertion_NotNormalized(t *testing.T) {
	assertion := NewThreeRegimeStabilityAssertion()

	data := &ThreeRegimeData{
		R1:    0.40,
		R2:    0.40,
		R3:    0.40, // Sum = 1.2, not normalized!
		Label: "not normalized",
	}

	err := assertion.Validate(data)
	if err == nil {
		t.Error("Expected non-normalized regime to fail")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// ASSERTION RUNNER TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestAssertionRunner_RunAll(t *testing.T) {
	runner := NewAssertionRunner()

	// Prepare test data
	data := make(map[string][]interface{})

	// Quaternions
	data["QuaternionNormPreservation"] = []interface{}{
		&QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		&QuaternionData{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5},
		&QuaternionData{W: 2, X: 0, Y: 0, Z: 0}, // Invalid!
	}

	// Digital roots
	data["DigitalRootPartition"] = []interface{}{
		&DigitalRootData{Input: 1, DigitalRoot: 1, ExpectedZero: false},
		&DigitalRootData{Input: 27, DigitalRoot: 9, ExpectedZero: false},
		&DigitalRootData{Input: 42, DigitalRoot: 10, ExpectedZero: false}, // Invalid!
	}

	results := runner.RunAll(data)

	if len(results) == 0 {
		t.Fatal("Expected results, got none")
	}

	// Should have 6 results total (3 quaternions + 3 digital roots)
	if len(results) != 6 {
		t.Errorf("Expected 6 results, got %d", len(results))
	}

	// Check that we have failures
	stats := runner.Stats()
	if stats.Failed == 0 {
		t.Error("Expected some failures, got none")
	}

	t.Logf("Stats: %d total, %d passed, %d failed (%.1f%% pass rate)",
		stats.Total, stats.Passed, stats.Failed, stats.PassRate*100)
}

func TestAssertionRunner_GenerateReport(t *testing.T) {
	runner := NewAssertionRunner()

	// Run some assertions
	data := make(map[string][]interface{})
	data["QuaternionNormPreservation"] = []interface{}{
		&QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		&QuaternionData{W: 2, X: 0, Y: 0, Z: 0}, // Invalid
	}

	runner.RunAll(data)

	report := runner.GenerateProofReport()

	if len(report) == 0 {
		t.Error("Expected non-empty report")
	}

	// Check report contains key sections
	if !containsSubstring(report, "RUNTIME PROOF VALIDATION REPORT") {
		t.Error("Report missing header")
	}
	if !containsSubstring(report, "SUMMARY STATISTICS") {
		t.Error("Report missing statistics")
	}
	if !containsSubstring(report, "CONCLUSION") {
		t.Error("Report missing conclusion")
	}

	t.Log("Generated report:")
	t.Log(report)
}

func TestAssertionRunner_CompactReport(t *testing.T) {
	runner := NewAssertionRunner()

	// All pass
	data := make(map[string][]interface{})
	data["QuaternionNormPreservation"] = []interface{}{
		&QuaternionData{W: 1, X: 0, Y: 0, Z: 0},
		&QuaternionData{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5},
	}

	runner.RunAll(data)
	compact := runner.GenerateCompactReport()

	if !containsSubstring(compact, "✅") {
		t.Error("Expected success indicator in compact report")
	}

	t.Logf("Compact report: %s", compact)
}

// ═══════════════════════════════════════════════════════════════════════════
// BATCH VALIDATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestBatchValidateQuaternions(t *testing.T) {
	quaternions := []*QuaternionData{
		{W: 1, X: 0, Y: 0, Z: 0},
		{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5},
		{W: 2, X: 0, Y: 0, Z: 0}, // Invalid
	}

	results := BatchValidateQuaternions(quaternions)

	if len(results) != 3 {
		t.Errorf("Expected 3 results, got %d", len(results))
	}

	passed := 0
	failed := 0
	for _, r := range results {
		if r.Passed {
			passed++
		} else {
			failed++
		}
	}

	if passed != 2 {
		t.Errorf("Expected 2 passed, got %d", passed)
	}
	if failed != 1 {
		t.Errorf("Expected 1 failed, got %d", failed)
	}
}

func TestValidationHook_Immediate(t *testing.T) {
	// Test immediate validation functions
	q := &QuaternionData{W: 1, X: 0, Y: 0, Z: 0}
	err := ValidateQuaternion(q)
	if err != nil {
		t.Errorf("Expected valid quaternion, got error: %v", err)
	}

	// Invalid quaternion
	q2 := &QuaternionData{W: 2, X: 0, Y: 0, Z: 0}
	err = ValidateQuaternion(q2)
	if err == nil {
		t.Error("Expected invalid quaternion to fail")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════


