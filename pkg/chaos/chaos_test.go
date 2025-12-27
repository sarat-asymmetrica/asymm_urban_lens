package chaos

import (
	"context"
	"errors"
	"strings"
	"testing"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS MONKEY UNIT TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosMonkey_InjectLatency(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.Enable()

	// Inject latency
	target := "gpu"
	delay := 100 * time.Millisecond
	monkey.InjectLatency(target, delay)

	// Verify latency applied
	ctx := context.Background()
	start := time.Now()
	err := monkey.Check(ctx, target)
	elapsed := time.Since(start)

	if err != nil {
		t.Errorf("Check returned error: %v", err)
	}

	if elapsed < delay {
		t.Errorf("Latency not applied: elapsed=%v, expected>=%v", elapsed, delay)
	}

	// Verify fault recorded
	faults := monkey.GetInjectedFaults()
	if len(faults) != 1 {
		t.Errorf("Expected 1 fault, got %d", len(faults))
	}

	if faults[0].Type != FaultLatency {
		t.Errorf("Fault type = %s, expected %s", faults[0].Type, FaultLatency)
	}
}

func TestChaosMonkey_InjectError(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.Enable()

	// Inject error
	target := "sonar:code"
	expectedErr := errors.New("code sonar unavailable")
	monkey.InjectError(target, expectedErr)

	// Verify error returned
	ctx := context.Background()
	err := monkey.Check(ctx, target)

	if err == nil {
		t.Error("Expected error, got nil")
	}

	if err.Error() != expectedErr.Error() {
		t.Errorf("Error = '%v', expected '%v'", err, expectedErr)
	}

	// Verify fault recorded
	faults := monkey.GetInjectedFaults()
	if len(faults) != 1 {
		t.Errorf("Expected 1 fault, got %d", len(faults))
	}

	if faults[0].Type != FaultError {
		t.Errorf("Fault type = %s, expected %s", faults[0].Type, FaultError)
	}
}

func TestChaosMonkey_InjectTimeout(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.Enable()

	// Inject timeout
	target := "api:openai"
	monkey.InjectTimeout(target)

	// Verify timeout hangs until context cancelled
	ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
	defer cancel()

	start := time.Now()
	err := monkey.Check(ctx, target)
	elapsed := time.Since(start)

	if err == nil {
		t.Error("Expected timeout error, got nil")
	}

	if elapsed < 50*time.Millisecond {
		t.Errorf("Timeout didn't wait: elapsed=%v", elapsed)
	}

	// Verify fault recorded
	faults := monkey.GetInjectedFaults()
	if len(faults) != 1 {
		t.Errorf("Expected 1 fault, got %d", len(faults))
	}

	if faults[0].Type != FaultTimeout {
		t.Errorf("Fault type = %s, expected %s", faults[0].Type, FaultTimeout)
	}
}

func TestChaosMonkey_InjectPartialFailure(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.Enable()

	// Inject 50% failure rate
	targets := []string{"sonar:ux"}
	failureRate := 0.5
	monkey.InjectPartialFailure(targets, failureRate)

	// Run 100 checks, expect ~50% failures (with tolerance)
	ctx := context.Background()
	failures := 0
	iterations := 100

	for i := 0; i < iterations; i++ {
		if err := monkey.Check(ctx, targets[0]); err != nil {
			failures++
		}
	}

	// Allow 20% tolerance (40-60% failure rate acceptable)
	expectedMin := int(float64(iterations) * failureRate * 0.8)
	expectedMax := int(float64(iterations) * failureRate * 1.2)

	if failures < expectedMin || failures > expectedMax {
		t.Errorf("Partial failure rate incorrect: %d/%d (expected %d-%d)",
			failures, iterations, expectedMin, expectedMax)
	}

	t.Logf("Partial failure rate: %d/%d = %.1f%% (target=%.1f%%)",
		failures, iterations, float64(failures)/float64(iterations)*100, failureRate*100)
}

func TestChaosMonkey_EnableDisable(t *testing.T) {
	monkey := NewChaosMonkey()

	// Inject error while disabled
	monkey.InjectError("gpu", errors.New("GPU failed"))

	// Check should return nil (chaos disabled)
	ctx := context.Background()
	err := monkey.Check(ctx, "gpu")
	if err != nil {
		t.Errorf("Expected nil (chaos disabled), got %v", err)
	}

	// Enable chaos
	monkey.Enable()
	err = monkey.Check(ctx, "gpu")
	if err == nil {
		t.Error("Expected error (chaos enabled), got nil")
	}

	// Disable chaos
	monkey.Disable()
	err = monkey.Check(ctx, "gpu")
	if err != nil {
		t.Errorf("Expected nil (chaos disabled), got %v", err)
	}
}

func TestChaosMonkey_ClearAll(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.Enable()

	// Inject multiple faults
	monkey.InjectLatency("gpu", 100*time.Millisecond)
	monkey.InjectError("sonar:code", errors.New("failed"))
	monkey.InjectTimeout("api:openai")

	// Verify faults exist
	faults := monkey.GetInjectedFaults()
	if len(faults) != 3 {
		t.Errorf("Expected 3 faults, got %d", len(faults))
	}

	// Clear all
	monkey.ClearAll()

	// Verify no more failures
	ctx := context.Background()
	if err := monkey.Check(ctx, "gpu"); err != nil {
		t.Errorf("Expected nil after ClearAll, got %v", err)
	}
	if err := monkey.Check(ctx, "sonar:code"); err != nil {
		t.Errorf("Expected nil after ClearAll, got %v", err)
	}

	// Note: Faults are still recorded (history), just no longer active
	faults = monkey.GetInjectedFaults()
	if len(faults) != 3 {
		t.Logf("Fault history preserved: %d faults", len(faults))
	}
}

func TestChaosMonkey_RecordRecovery(t *testing.T) {
	monkey := NewChaosMonkey()

	// Inject fault
	target := "gpu"
	monkey.InjectError(target, errors.New("GPU unavailable"))

	// Wait a tiny bit to ensure time passes
	time.Sleep(1 * time.Millisecond)

	// Record recovery
	mitigation := "CPU fallback activated"
	monkey.RecordRecovery(target, mitigation)

	// Verify recovery recorded
	faults := monkey.GetInjectedFaults()
	if len(faults) != 1 {
		t.Fatalf("Expected 1 fault, got %d", len(faults))
	}

	fault := faults[0]
	if !fault.Recovered {
		t.Error("Fault not marked as recovered")
	}

	if fault.Mitigation != mitigation {
		t.Errorf("Mitigation = '%s', expected '%s'", fault.Mitigation, mitigation)
	}

	if fault.Duration == 0 {
		t.Error("Duration not calculated")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS SCENARIO TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestScenario_GPUFailure(t *testing.T) {
	monkey := NewChaosMonkey()
	scenario := ScenarioGPUFailure()

	// Apply scenario
	scenario.Apply(monkey)
	monkey.Enable()

	// Verify GPU operations fail
	ctx := context.Background()
	if err := monkey.Check(ctx, "gpu"); err == nil {
		t.Error("Expected GPU failure, got nil")
	}
	if err := monkey.Check(ctx, "gpu:quaternion"); err == nil {
		t.Error("Expected GPU quaternion failure, got nil")
	}
	if err := monkey.Check(ctx, "gpu:vqc"); err == nil {
		t.Error("Expected GPU VQC failure, got nil")
	}

	// Simulate recovery (CPU fallback)
	monkey.RecordRecovery("gpu", "CPU fallback activated")

	// Validate scenario
	if err := scenario.Validate(monkey); err != nil {
		t.Errorf("Scenario validation failed: %v", err)
	}
}

func TestScenario_SonarPartialOutage(t *testing.T) {
	monkey := NewChaosMonkey()
	n := 3 // Fail 3 out of 6 sonars
	scenario := ScenarioSonarPartialOutage(n)

	// Apply scenario
	scenario.Apply(monkey)
	monkey.Enable()

	// Verify exactly N sonars fail
	ctx := context.Background()
	sonars := []string{"code", "ux", "design", "journey", "state", "semantic"}
	failures := 0
	for _, sonar := range sonars {
		if err := monkey.Check(ctx, "sonar:"+sonar); err != nil {
			failures++
		}
	}

	if failures != n {
		t.Errorf("Expected %d sonar failures, got %d", n, failures)
	}

	// Validate scenario
	if err := scenario.Validate(monkey); err != nil {
		t.Errorf("Scenario validation failed: %v", err)
	}
}

func TestScenario_NetworkLatency(t *testing.T) {
	monkey := NewChaosMonkey()
	delay := 50 * time.Millisecond
	scenario := ScenarioNetworkLatency(delay)

	// Apply scenario
	scenario.Apply(monkey)
	monkey.Enable()

	// Verify latency applied
	ctx := context.Background()
	start := time.Now()
	_ = monkey.Check(ctx, "api:openai")
	elapsed := time.Since(start)

	if elapsed < delay {
		t.Errorf("Latency not applied: elapsed=%v, expected>=%v", elapsed, delay)
	}

	// Validate scenario
	if err := scenario.Validate(monkey); err != nil {
		t.Errorf("Scenario validation failed: %v", err)
	}
}

func TestScenario_APITimeout(t *testing.T) {
	monkey := NewChaosMonkey()
	scenario := ScenarioAPITimeout()

	// Apply scenario
	scenario.Apply(monkey)
	monkey.Enable()

	// Verify timeout triggers context cancellation
	ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
	defer cancel()

	err := monkey.Check(ctx, "api:openai")
	if err == nil {
		t.Error("Expected timeout error, got nil")
	}

	// Validate scenario
	if err := scenario.Validate(monkey); err != nil {
		t.Errorf("Scenario validation failed: %v", err)
	}
}

func TestScenario_MemoryPressure(t *testing.T) {
	monkey := NewChaosMonkey()
	scenario := ScenarioMemoryPressure()

	// Apply scenario
	scenario.Apply(monkey)
	monkey.Enable()

	// Verify memory operations fail
	ctx := context.Background()
	if err := monkey.Check(ctx, "memory"); err == nil {
		t.Error("Expected memory error, got nil")
	}
	if err := monkey.Check(ctx, "alloc:large"); err == nil {
		t.Error("Expected allocation error, got nil")
	}

	// Validate scenario
	if err := scenario.Validate(monkey); err != nil {
		t.Errorf("Scenario validation failed: %v", err)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS CONTROLLER TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestChaosController_StartStop(t *testing.T) {
	monkey := NewChaosMonkey()
	controller := NewChaosController(monkey)

	// Start scenario
	scenario := ScenarioGPUFailure()
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	if !controller.IsRunning() {
		t.Error("Controller should be running")
	}

	// Verify scenario applied
	ctx := context.Background()
	if err := monkey.Check(ctx, "gpu"); err == nil {
		t.Error("Expected GPU failure, got nil")
	}

	// Simulate recovery
	monkey.RecordRecovery("gpu", "CPU fallback")

	// Stop scenario
	if err := controller.Stop(); err != nil {
		t.Errorf("Stop failed: %v", err)
	}

	if controller.IsRunning() {
		t.Error("Controller should not be running")
	}
}

func TestChaosController_CannotStartTwice(t *testing.T) {
	monkey := NewChaosMonkey()
	controller := NewChaosController(monkey)

	// Start first scenario
	scenario1 := ScenarioGPUFailure()
	if err := controller.Start(scenario1); err != nil {
		t.Fatalf("First Start failed: %v", err)
	}

	// Try starting second scenario (should fail)
	scenario2 := ScenarioNetworkLatency(100 * time.Millisecond)
	err := controller.Start(scenario2)
	if err == nil {
		t.Error("Expected error starting second scenario, got nil")
	}

	if !strings.Contains(err.Error(), "already running") {
		t.Errorf("Error should mention 'already running', got: %v", err)
	}
}

func TestChaosController_GetInjectedFaults(t *testing.T) {
	monkey := NewChaosMonkey()
	controller := NewChaosController(monkey)

	// Start scenario
	scenario := ScenarioSonarPartialOutage(2)
	if err := controller.Start(scenario); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	// Get faults
	faults := controller.GetInjectedFaults()
	if len(faults) != 2 {
		t.Errorf("Expected 2 faults, got %d", len(faults))
	}

	// Verify fault details
	for _, fault := range faults {
		if !strings.HasPrefix(fault.Target, "sonar:") {
			t.Errorf("Expected sonar fault, got target: %s", fault.Target)
		}
		if fault.Type != FaultError {
			t.Errorf("Expected error fault, got: %s", fault.Type)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// RECOVERY AND GRACEFUL DEGRADATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestRecovery_GPUFallbackToCPU(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.InjectError("gpu", errors.New("GPU unavailable"))
	monkey.Enable()

	ctx := context.Background()

	// Attempt GPU operation
	err := monkey.Check(ctx, "gpu")
	if err == nil {
		t.Fatal("Expected GPU error, got nil")
	}

	// Simulate fallback to CPU
	cpuErr := monkey.Check(ctx, "cpu") // CPU should work
	if cpuErr != nil {
		t.Errorf("CPU fallback failed: %v", cpuErr)
	}

	// Record recovery
	monkey.RecordRecovery("gpu", "CPU fallback successful")

	// Verify recovery recorded
	faults := monkey.GetInjectedFaults()
	found := false
	for _, f := range faults {
		if f.Target == "gpu" && f.Recovered {
			found = true
			if f.Mitigation != "CPU fallback successful" {
				t.Errorf("Mitigation = '%s', expected 'CPU fallback successful'", f.Mitigation)
			}
		}
	}

	if !found {
		t.Error("GPU recovery not recorded")
	}
}

func TestRecovery_PartialSonarResults(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.InjectError("sonar:code", errors.New("code sonar failed"))
	monkey.InjectError("sonar:ux", errors.New("ux sonar failed"))
	monkey.Enable()

	ctx := context.Background()
	sonars := []string{"code", "ux", "design", "journey", "state", "semantic"}

	// Attempt all sonars
	successful := []string{}
	failed := []string{}

	for _, sonar := range sonars {
		if err := monkey.Check(ctx, "sonar:"+sonar); err != nil {
			failed = append(failed, sonar)
		} else {
			successful = append(successful, sonar)
		}
	}

	// Verify partial results
	if len(failed) != 2 {
		t.Errorf("Expected 2 failures, got %d", len(failed))
	}

	if len(successful) != 4 {
		t.Errorf("Expected 4 successes, got %d", len(successful))
	}

	// Verify system can continue with partial results
	t.Logf("Partial results: %d/%d sonars succeeded", len(successful), len(sonars))
	t.Logf("Failed: %v", failed)
	t.Logf("Successful: %v", successful)
}

func TestRecovery_TimeoutWithContext(t *testing.T) {
	monkey := NewChaosMonkey()
	monkey.InjectTimeout("api:openai")
	monkey.Enable()

	// Create context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	start := time.Now()
	err := monkey.Check(ctx, "api:openai")
	elapsed := time.Since(start)

	// Verify timeout triggered
	if err == nil {
		t.Error("Expected timeout error, got nil")
	}

	if elapsed < 100*time.Millisecond {
		t.Errorf("Timeout too fast: %v", elapsed)
	}

	// Verify context error
	if !errors.Is(err, context.DeadlineExceeded) {
		t.Logf("Error type: %T, value: %v", err, err)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// LOGGING AND OBSERVABILITY TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestLogging_FaultInjection(t *testing.T) {
	monkey := NewChaosMonkey()

	// Capture logs
	logs := []string{}
	monkey.logger = func(msg string) {
		logs = append(logs, msg)
	}

	// Inject various faults
	monkey.InjectLatency("gpu", 100*time.Millisecond)
	monkey.InjectError("sonar:code", errors.New("failed"))
	monkey.InjectTimeout("api:openai")

	// Verify logs
	if len(logs) != 3 {
		t.Errorf("Expected 3 log messages, got %d", len(logs))
	}

	// Check log content
	hasLatency := false
	hasError := false
	hasTimeout := false

	for _, log := range logs {
		if strings.Contains(log, "latency") {
			hasLatency = true
		}
		if strings.Contains(log, "error") {
			hasError = true
		}
		if strings.Contains(log, "timeout") {
			hasTimeout = true
		}
	}

	if !hasLatency {
		t.Error("Missing latency log")
	}
	if !hasError {
		t.Error("Missing error log")
	}
	if !hasTimeout {
		t.Error("Missing timeout log")
	}

	t.Logf("Logs captured: %v", logs)
}

func TestLogging_Recovery(t *testing.T) {
	monkey := NewChaosMonkey()

	// Capture logs
	logs := []string{}
	monkey.logger = func(msg string) {
		logs = append(logs, msg)
	}

	// Inject and recover
	monkey.InjectError("gpu", errors.New("GPU failed"))
	monkey.RecordRecovery("gpu", "CPU fallback")

	// Verify recovery logged
	hasRecovery := false
	for _, log := range logs {
		if strings.Contains(log, "Recovery") || strings.Contains(log, "recovered") {
			hasRecovery = true
		}
	}

	if !hasRecovery {
		t.Error("Recovery not logged")
	}

	t.Logf("Logs: %v", logs)
}
