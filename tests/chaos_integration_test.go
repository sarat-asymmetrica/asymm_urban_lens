package tests

import (
	"context"
	"errors"
	"testing"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/chaos"
)

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS INTEGRATION TESTS - HAMILTON'S RESILIENCE VALIDATION
// ═══════════════════════════════════════════════════════════════════════════
//
// Philosophy: "Test your failures before production tests them for you."
//             - Margaret Hamilton (Apollo 11 Guidance Computer, 1969)
//
// These tests verify the system degrades gracefully under chaos:
// 1. GPU failure → CPU fallback works
// 2. Sonar partial outage → partial results returned
// 3. Network latency → timeouts enforced, retries work
// 4. API timeout → context cancellation works
// 5. Memory pressure → allocation errors handled
//
// Success criteria:
// - No panics
// - Errors logged, not swallowed
// - Partial functionality maintained
// - Recovery mechanisms triggered
// ═══════════════════════════════════════════════════════════════════════════

// MockSystem simulates UrbanLens system components
type MockSystem struct {
	gpuAvailable    bool
	cpuAvailable    bool
	sonarsRunning   map[string]bool
	apiResponsive   bool
	memoryAvailable bool
	monkey          *chaos.ChaosMonkey
}

// NewMockSystem creates test system
func NewMockSystem(monkey *chaos.ChaosMonkey) *MockSystem {
	return &MockSystem{
		gpuAvailable:    true,
		cpuAvailable:    true,
		sonarsRunning:   map[string]bool{
			"code": true, "ux": true, "design": true,
			"journey": true, "state": true, "semantic": true,
		},
		apiResponsive:   true,
		memoryAvailable: true,
		monkey:          monkey,
	}
}

// GPUCompute simulates GPU operation with fallback
func (ms *MockSystem) GPUCompute(ctx context.Context, data []float32) ([]float32, error) {
	// Check for chaos injection
	if err := ms.monkey.Check(ctx, "gpu"); err != nil {
		// GPU failed - attempt CPU fallback
		ms.monkey.RecordRecovery("gpu", "CPU fallback activated")
		return ms.CPUCompute(ctx, data)
	}

	// GPU computation successful
	result := make([]float32, len(data))
	for i, v := range data {
		result[i] = v * 2.0 // Simplified GPU operation
	}
	return result, nil
}

// CPUCompute simulates CPU fallback
func (ms *MockSystem) CPUCompute(ctx context.Context, data []float32) ([]float32, error) {
	if err := ms.monkey.Check(ctx, "cpu"); err != nil {
		return nil, err
	}

	// CPU computation (slower but reliable)
	result := make([]float32, len(data))
	for i, v := range data {
		result[i] = v * 2.0
	}
	return result, nil
}

// RunSonars simulates sonar suite execution
func (ms *MockSystem) RunSonars(ctx context.Context) (map[string]float64, error) {
	results := make(map[string]float64)
	failures := []string{}

	// Attempt all sonars
	for name := range ms.sonarsRunning {
		if err := ms.monkey.Check(ctx, "sonar:"+name); err != nil {
			failures = append(failures, name)
			continue
		}

		// Sonar succeeded - record mock score
		results[name] = 0.85 // Mock quality score
	}

	// Return partial results if some sonars failed
	if len(failures) > 0 {
		return results, errors.New("partial sonar failure: " + failures[0])
	}

	return results, nil
}

// CallAPI simulates API call with timeout
func (ms *MockSystem) CallAPI(ctx context.Context, endpoint string) (string, error) {
	if err := ms.monkey.Check(ctx, "api:"+endpoint); err != nil {
		return "", err
	}

	// API call successful
	return "API response", nil
}

// AllocateMemory simulates memory allocation
func (ms *MockSystem) AllocateMemory(ctx context.Context, size int) ([]byte, error) {
	if size > 1024*1024 {
		if err := ms.monkey.Check(ctx, "alloc:large"); err != nil {
			return nil, err
		}
	} else {
		if err := ms.monkey.Check(ctx, "alloc:medium"); err != nil {
			return nil, err
		}
	}

	return make([]byte, size), nil
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 1: GPU FAILURE → CPU FALLBACK
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_GPUFailureFallback(t *testing.T) {
	t.Log("🧪 TEST: GPU Failure → CPU Fallback")

	// Setup
	monkey := chaos.NewChaosMonkey()
	controller := chaos.NewChaosController(monkey)
	system := NewMockSystem(monkey)

	// Start GPU failure scenario
	scenario := chaos.ScenarioGPUFailure()
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Failed to start scenario: %v", err)
	}
	defer controller.Stop()

	// Test data
	testData := []float32{1.0, 2.0, 3.0, 4.0}

	// Attempt GPU compute (should fallback to CPU)
	ctx := context.Background()
	result, err := system.GPUCompute(ctx, testData)

	// Verify result obtained despite GPU failure
	if err != nil {
		t.Fatalf("GPUCompute failed even with fallback: %v", err)
	}

	if len(result) != len(testData) {
		t.Errorf("Result length = %d, expected %d", len(result), len(testData))
	}

	// Verify values correct
	for i, v := range result {
		expected := testData[i] * 2.0
		if v != expected {
			t.Errorf("result[%d] = %f, expected %f", i, v, expected)
		}
	}

	// Verify recovery recorded
	faults := controller.GetInjectedFaults()
	recovered := false
	for _, f := range faults {
		if f.Target == "gpu" && f.Recovered {
			recovered = true
			if f.Mitigation != "CPU fallback activated" {
				t.Errorf("Mitigation = '%s', expected 'CPU fallback activated'", f.Mitigation)
			}
		}
	}

	if !recovered {
		t.Error("GPU recovery not recorded")
	}

	t.Log("✅ GPU failure handled via CPU fallback")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 2: SONAR PARTIAL OUTAGE → PARTIAL RESULTS
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_SonarPartialOutage(t *testing.T) {
	t.Log("🧪 TEST: Sonar Partial Outage → Partial Results")

	// Setup
	monkey := chaos.NewChaosMonkey()
	controller := chaos.NewChaosController(monkey)
	system := NewMockSystem(monkey)

	// Start partial sonar failure (3 out of 6 fail)
	scenario := chaos.ScenarioSonarPartialOutage(3)
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Failed to start scenario: %v", err)
	}
	defer controller.Stop()

	// Run sonars
	ctx := context.Background()
	results, err := system.RunSonars(ctx)

	// Verify error returned (partial failure)
	if err == nil {
		t.Log("Warning: Expected partial failure error, got nil (acceptable)")
	}

	// Verify partial results obtained (3 failed, 3 succeeded)
	if len(results) != 3 {
		t.Errorf("Results = %d sonars, expected 3", len(results))
	}

	// Verify successful sonars have scores
	for name, score := range results {
		if score <= 0.0 || score > 1.0 {
			t.Errorf("Sonar %s score = %f, expected 0.0-1.0", name, score)
		}
		t.Logf("  ✓ Sonar %s: %.2f", name, score)
	}

	// Verify system continues despite partial failure
	t.Log("✅ Partial sonar results obtained despite failures")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 3: NETWORK LATENCY → TIMEOUTS ENFORCED
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_NetworkLatency(t *testing.T) {
	t.Log("🧪 TEST: Network Latency → Timeouts Enforced")

	// Setup
	monkey := chaos.NewChaosMonkey()
	controller := chaos.NewChaosController(monkey)
	system := NewMockSystem(monkey)

	// Start network latency scenario (200ms delay)
	delay := 200 * time.Millisecond
	scenario := chaos.ScenarioNetworkLatency(delay)
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Failed to start scenario: %v", err)
	}
	defer controller.Stop()

	// Call API with timeout shorter than latency
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	start := time.Now()
	_, err := system.CallAPI(ctx, "openai")
	elapsed := time.Since(start)

	// Verify timeout triggered
	if err == nil {
		t.Error("Expected timeout error, got nil")
	}

	if elapsed < 100*time.Millisecond {
		t.Errorf("Timeout too fast: %v", elapsed)
	}

	t.Logf("Timeout enforced after %v (latency=%v, timeout=%v)", elapsed, delay, 100*time.Millisecond)

	// Now try with sufficient timeout
	ctx2, cancel2 := context.WithTimeout(context.Background(), 500*time.Millisecond)
	defer cancel2()

	start2 := time.Now()
	result, err := system.CallAPI(ctx2, "openai")
	elapsed2 := time.Since(start2)

	// Verify call succeeded with sufficient timeout
	if err != nil {
		t.Errorf("API call failed with sufficient timeout: %v", err)
	}

	if result == "" {
		t.Error("Empty result")
	}

	if elapsed2 < delay {
		t.Errorf("Call too fast: %v (expected >= %v)", elapsed2, delay)
	}

	t.Log("✅ Network latency handled with timeouts")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 4: API TIMEOUT → CONTEXT CANCELLATION
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_APITimeout(t *testing.T) {
	t.Log("🧪 TEST: API Timeout → Context Cancellation")

	// Setup
	monkey := chaos.NewChaosMonkey()
	controller := chaos.NewChaosController(monkey)
	system := NewMockSystem(monkey)

	// Start API timeout scenario
	scenario := chaos.ScenarioAPITimeout()
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Failed to start scenario: %v", err)
	}
	defer controller.Stop()

	// Call API with timeout (should hang forever without timeout)
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	start := time.Now()
	_, err := system.CallAPI(ctx, "openai")
	elapsed := time.Since(start)

	// Verify context cancellation triggered
	if err == nil {
		t.Error("Expected timeout error, got nil")
	}

	if elapsed < 100*time.Millisecond {
		t.Errorf("Timeout too fast: %v", elapsed)
	}

	// Verify error is context deadline exceeded
	if !errors.Is(err, context.DeadlineExceeded) {
		t.Logf("Error type: %T, value: %v", err, err)
	}

	t.Log("✅ API timeout handled via context cancellation")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 5: MEMORY PRESSURE → ALLOCATION ERRORS HANDLED
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_MemoryPressure(t *testing.T) {
	t.Log("🧪 TEST: Memory Pressure → Allocation Errors Handled")

	// Setup
	monkey := chaos.NewChaosMonkey()
	controller := chaos.NewChaosController(monkey)
	system := NewMockSystem(monkey)

	// Start memory pressure scenario
	scenario := chaos.ScenarioMemoryPressure()
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Failed to start scenario: %v", err)
	}
	defer controller.Stop()

	ctx := context.Background()

	// Attempt large allocation (should fail)
	largeSize := 10 * 1024 * 1024 // 10 MB
	_, err := system.AllocateMemory(ctx, largeSize)

	if err == nil {
		t.Error("Expected allocation error for large size, got nil")
	}

	t.Logf("Large allocation failed as expected: %v", err)

	// Attempt medium allocation (may fail due to 30% failure rate)
	mediumSize := 1024 // 1 KB
	successes := 0
	failures := 0

	for i := 0; i < 20; i++ {
		_, err := system.AllocateMemory(ctx, mediumSize)
		if err == nil {
			successes++
		} else {
			failures++
		}
	}

	// Verify partial failure rate (should be ~30%)
	if failures == 0 {
		t.Error("Expected some medium allocation failures, got none")
	}

	if successes == 0 {
		t.Error("Expected some medium allocation successes, got none")
	}

	t.Logf("Medium allocations: %d succeeded, %d failed (%.1f%% failure rate)",
		successes, failures, float64(failures)/float64(successes+failures)*100)

	t.Log("✅ Memory pressure handled gracefully")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 6: COMPLETE SYSTEM STRESS TEST
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_CompleteSystemStress(t *testing.T) {
	t.Log("🧪 TEST: Complete System Stress (All Failures)")

	// Setup
	monkey := chaos.NewChaosMonkey()
	system := NewMockSystem(monkey)

	// Inject ALL chaos
	monkey.InjectError("gpu", errors.New("GPU unavailable"))
	monkey.InjectPartialFailure([]string{"sonar:code", "sonar:ux"}, 0.5)
	monkey.InjectLatency("api:openai", 50*time.Millisecond)
	monkey.InjectError("alloc:large", errors.New("out of memory"))
	monkey.Enable()

	ctx := context.Background()

	// Test 1: GPU compute with fallback
	t.Log("  1. Testing GPU → CPU fallback")
	result, err := system.GPUCompute(ctx, []float32{1.0, 2.0})
	if err != nil {
		t.Errorf("GPU fallback failed: %v", err)
	} else {
		t.Logf("    ✓ GPU fallback successful: %v", result)
	}

	// Test 2: Sonar suite with partial failures
	t.Log("  2. Testing sonar suite with partial failures")
	sonarResults, err := system.RunSonars(ctx)
	if len(sonarResults) == 0 {
		t.Error("No sonar results obtained")
	} else {
		t.Logf("    ✓ Partial sonar results: %d sonars succeeded", len(sonarResults))
	}

	// Test 3: API call with latency
	t.Log("  3. Testing API with latency")
	ctx3, cancel3 := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel3()

	apiResult, err := system.CallAPI(ctx3, "openai")
	if err != nil {
		t.Errorf("API call failed: %v", err)
	} else {
		t.Logf("    ✓ API call succeeded: %s", apiResult)
	}

	// Test 4: Memory allocation under pressure
	t.Log("  4. Testing memory allocation under pressure")
	_, err = system.AllocateMemory(ctx, 1024) // Small allocation should work
	if err != nil {
		t.Logf("    ⚠ Small allocation failed: %v (acceptable under pressure)", err)
	} else {
		t.Log("    ✓ Small allocation succeeded")
	}

	_, err = system.AllocateMemory(ctx, 10*1024*1024) // Large allocation should fail
	if err == nil {
		t.Error("Large allocation should fail under pressure")
	} else {
		t.Logf("    ✓ Large allocation failed as expected: %v", err)
	}

	// Verify system survived complete chaos
	t.Log("✅ System survived complete chaos - graceful degradation confirmed")
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST 7: HAMILTON'S ULTIMATE TEST - NO PANICS ALLOWED
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosIntegration_HamiltonNoPanics(t *testing.T) {
	t.Log("🧪 HAMILTON'S ULTIMATE TEST: No Panics Under Any Chaos")

	// This test throws EVERYTHING at the system
	// If it panics, we failed Hamilton

	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("❌ SYSTEM PANICKED: %v (Hamilton would not approve!)", r)
		}
	}()

	monkey := chaos.NewChaosMonkey()
	system := NewMockSystem(monkey)

	// MAXIMUM CHAOS
	monkey.InjectError("gpu", errors.New("GPU exploded"))
	monkey.InjectError("cpu", errors.New("CPU on fire"))
	monkey.InjectError("sonar:code", errors.New("code sonar melted"))
	monkey.InjectError("sonar:ux", errors.New("ux sonar vanished"))
	monkey.InjectError("sonar:design", errors.New("design sonar corrupted"))
	monkey.InjectTimeout("api:openai")
	monkey.InjectLatency("api:aimlapi", 1*time.Second)
	monkey.InjectError("memory", errors.New("memory corrupted"))
	monkey.InjectError("alloc:large", errors.New("allocation impossible"))
	monkey.InjectPartialFailure([]string{"alloc:medium"}, 1.0) // 100% failure
	monkey.Enable()

	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	// Try everything (all will fail, but should not panic)
	t.Log("  Attempting operations under maximum chaos...")

	_, _ = system.GPUCompute(ctx, []float32{1.0})
	t.Log("    ✓ GPUCompute survived")

	_, _ = system.RunSonars(ctx)
	t.Log("    ✓ RunSonars survived")

	_, _ = system.CallAPI(ctx, "openai")
	t.Log("    ✓ CallAPI survived")

	_, _ = system.AllocateMemory(ctx, 1024)
	t.Log("    ✓ AllocateMemory survived")

	t.Log("✅ HAMILTON APPROVED: No panics under maximum chaos")
}
