package resilience

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// TestStateTransitions verifies state machine follows correct transitions
func TestStateTransitions(t *testing.T) {
	tests := []struct {
		name               string
		failureThreshold   uint32
		successThreshold   uint32
		timeout            time.Duration
		operations         []bool // true = success, false = failure
		expectedFinalState State
		expectedStats      func(Stats) bool
	}{
		{
			name:               "Closed -> Open after failures",
			failureThreshold:   3,
			successThreshold:   2,
			timeout:            100 * time.Millisecond,
			operations:         []bool{false, false, false}, // 3 failures
			expectedFinalState: StateOpen,
			expectedStats: func(s Stats) bool {
				return s.TotalFailures == 3 && s.State == StateOpen
			},
		},
		{
			name:               "Stay Closed with mixed results",
			failureThreshold:   5,
			successThreshold:   2,
			timeout:            100 * time.Millisecond,
			operations:         []bool{true, false, true, false}, // Not enough consecutive failures
			expectedFinalState: StateClosed,
			expectedStats: func(s Stats) bool {
				return s.TotalSuccesses == 2 && s.TotalFailures == 2 && s.State == StateClosed
			},
		},
		{
			name:               "Open -> HalfOpen -> Closed with timeout",
			failureThreshold:   2,
			successThreshold:   2,
			timeout:            50 * time.Millisecond,
			operations:         []bool{false, false}, // Opens circuit
			expectedFinalState: StateOpen,
			expectedStats: func(s Stats) bool {
				return s.State == StateOpen && s.ConsecutiveFailures == 0
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			config := Config{
				Name:                  tt.name,
				FailureThreshold:      tt.failureThreshold,
				SuccessThreshold:      tt.successThreshold,
				Timeout:               tt.timeout,
				MaxConcurrentRequests: 1,
			}

			cb, err := NewCircuitBreaker(tt.name, config)
			if err != nil {
				t.Fatalf("Failed to create circuit breaker: %v", err)
			}

			// Execute operations
			for i, shouldSucceed := range tt.operations {
				fn := func() error {
					if shouldSucceed {
						return nil
					}
					return errors.New("simulated failure")
				}

				err := cb.Execute(fn)
				t.Logf("Operation %d: success=%v, err=%v, state=%v", i, shouldSucceed, err, cb.GetState())
			}

			// Verify final state
			finalState := cb.GetState()
			if finalState != tt.expectedFinalState {
				t.Errorf("Expected final state %v, got %v", tt.expectedFinalState, finalState)
			}

			// Verify stats
			stats := cb.GetStats()
			if !tt.expectedStats(stats) {
				t.Errorf("Stats validation failed: %+v", stats)
			}
		})
	}
}

// TestOpenToHalfOpenTransition verifies timeout-based state transition
func TestOpenToHalfOpenTransition(t *testing.T) {
	config := Config{
		Name:                  "timeout-test",
		FailureThreshold:      2,
		SuccessThreshold:      2,
		Timeout:               100 * time.Millisecond,
		MaxConcurrentRequests: 1,
	}

	cb, err := NewCircuitBreaker("timeout-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Trigger failures to open circuit
	failFn := func() error { return errors.New("fail") }
	cb.Execute(failFn)
	cb.Execute(failFn)

	if cb.GetState() != StateOpen {
		t.Fatalf("Expected state OPEN after failures, got %v", cb.GetState())
	}

	// Try immediate execution - should be blocked
	err = cb.Execute(func() error { return nil })
	if !errors.Is(err, ErrCircuitOpen) {
		t.Errorf("Expected ErrCircuitOpen immediately, got %v", err)
	}

	// Wait for timeout
	time.Sleep(150 * time.Millisecond)

	// Next request should transition to half-open and execute
	executed := false
	err = cb.Execute(func() error {
		executed = true
		return nil
	})

	if err != nil {
		t.Errorf("Expected successful execution after timeout, got error: %v", err)
	}
	if !executed {
		t.Error("Function was not executed after timeout")
	}

	state := cb.GetState()
	if state != StateHalfOpen && state != StateClosed {
		t.Errorf("Expected state HALF_OPEN or CLOSED after timeout, got %v", state)
	}
}

// TestHalfOpenToClosed verifies recovery path
func TestHalfOpenToClosed(t *testing.T) {
	config := Config{
		Name:                  "recovery-test",
		FailureThreshold:      2,
		SuccessThreshold:      3,
		Timeout:               50 * time.Millisecond,
		MaxConcurrentRequests: 1,
	}

	cb, err := NewCircuitBreaker("recovery-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Open circuit
	failFn := func() error { return errors.New("fail") }
	cb.Execute(failFn)
	cb.Execute(failFn)

	if cb.GetState() != StateOpen {
		t.Fatalf("Expected state OPEN, got %v", cb.GetState())
	}

	// Wait for timeout to transition to half-open
	time.Sleep(100 * time.Millisecond)

	// Execute successful requests
	successFn := func() error { return nil }
	for i := 0; i < 3; i++ {
		err := cb.Execute(successFn)
		if err != nil {
			t.Errorf("Request %d failed: %v", i, err)
		}
		t.Logf("Request %d: state=%v", i, cb.GetState())
	}

	// Should be closed now
	finalState := cb.GetState()
	if finalState != StateClosed {
		t.Errorf("Expected state CLOSED after successful recovery, got %v", finalState)
	}

	stats := cb.GetStats()
	if stats.TotalSuccesses < uint64(config.SuccessThreshold) {
		t.Errorf("Expected at least %d total successes, got %d",
			config.SuccessThreshold, stats.TotalSuccesses)
	}
}

// TestHalfOpenToOpenOnFailure verifies failure in half-open reopens circuit
func TestHalfOpenToOpenOnFailure(t *testing.T) {
	config := Config{
		Name:                  "reopen-test",
		FailureThreshold:      2,
		SuccessThreshold:      2,
		Timeout:               50 * time.Millisecond,
		MaxConcurrentRequests: 1,
	}

	cb, err := NewCircuitBreaker("reopen-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Open circuit
	failFn := func() error { return errors.New("fail") }
	cb.Execute(failFn)
	cb.Execute(failFn)

	// Wait for timeout
	time.Sleep(100 * time.Millisecond)

	// Execute one successful request (should be half-open now)
	cb.Execute(func() error { return nil })

	state := cb.GetState()
	if state != StateHalfOpen && state != StateClosed {
		t.Logf("Warning: Expected HALF_OPEN, got %v (might have closed already)", state)
	}

	// Fail again - should reopen
	cb.Execute(failFn)

	finalState := cb.GetState()
	if finalState != StateOpen {
		t.Errorf("Expected state OPEN after failure in half-open, got %v", finalState)
	}
}

// TestThresholdEnforcement verifies thresholds are correctly enforced
func TestThresholdEnforcement(t *testing.T) {
	tests := []struct {
		name             string
		failureThreshold uint32
		successThreshold uint32
		operations       []bool
		expectedState    State
	}{
		{
			name:             "Just below failure threshold",
			failureThreshold: 5,
			successThreshold: 2,
			operations:       []bool{false, false, false, false}, // 4 failures, threshold is 5
			expectedState:    StateClosed,
		},
		{
			name:             "Exactly at failure threshold",
			failureThreshold: 5,
			successThreshold: 2,
			operations:       []bool{false, false, false, false, false}, // 5 failures
			expectedState:    StateOpen,
		},
		{
			name:             "Success resets failure counter",
			failureThreshold: 3,
			successThreshold: 2,
			operations:       []bool{false, false, true, false, false}, // Success breaks streak
			expectedState:    StateClosed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			config := Config{
				Name:                  tt.name,
				FailureThreshold:      tt.failureThreshold,
				SuccessThreshold:      tt.successThreshold,
				Timeout:               100 * time.Millisecond,
				MaxConcurrentRequests: 1,
			}

			cb, err := NewCircuitBreaker(tt.name, config)
			if err != nil {
				t.Fatalf("Failed to create circuit breaker: %v", err)
			}

			for _, shouldSucceed := range tt.operations {
				fn := func() error {
					if shouldSucceed {
						return nil
					}
					return errors.New("fail")
				}
				cb.Execute(fn)
			}

			state := cb.GetState()
			if state != tt.expectedState {
				t.Errorf("Expected state %v, got %v", tt.expectedState, state)
			}
		})
	}
}

// TestThreadSafety verifies circuit breaker handles concurrent requests safely
func TestThreadSafety(t *testing.T) {
	config := Config{
		Name:                  "concurrent-test",
		FailureThreshold:      10,
		SuccessThreshold:      5,
		Timeout:               100 * time.Millisecond,
		MaxConcurrentRequests: 10,
	}

	cb, err := NewCircuitBreaker("concurrent-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	var (
		wg              sync.WaitGroup
		successCount    int64
		failureCount    int64
		blockedCount    int64
		numGoroutines   = 100
		requestsPerGoro = 100
	)

	// Launch concurrent goroutines
	for i := 0; i < numGoroutines; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()

			for j := 0; j < requestsPerGoro; j++ {
				// Simulate random success/failure
				shouldSucceed := (id+j)%3 != 0

				fn := func() error {
					time.Sleep(1 * time.Millisecond) // Simulate work
					if shouldSucceed {
						return nil
					}
					return errors.New("fail")
				}

				err := cb.Execute(fn)
				if err == nil {
					atomic.AddInt64(&successCount, 1)
				} else if errors.Is(err, ErrCircuitOpen) || errors.Is(err, ErrTooManyRequests) {
					atomic.AddInt64(&blockedCount, 1)
				} else {
					atomic.AddInt64(&failureCount, 1)
				}
			}
		}(i)
	}

	wg.Wait()

	// Verify stats consistency
	stats := cb.GetStats()
	totalProcessed := successCount + failureCount
	totalRequests := stats.TotalRequests

	t.Logf("Total requests: %d", totalRequests)
	t.Logf("Successes: %d", successCount)
	t.Logf("Failures: %d", failureCount)
	t.Logf("Blocked: %d", blockedCount)
	t.Logf("Stats: %+v", stats)

	// Basic sanity checks
	if totalRequests == 0 {
		t.Error("No requests were processed")
	}

	if stats.TotalSuccesses != uint64(successCount) {
		t.Errorf("Success count mismatch: stats=%d, actual=%d",
			stats.TotalSuccesses, successCount)
	}

	if stats.TotalFailures != uint64(failureCount) {
		t.Errorf("Failure count mismatch: stats=%d, actual=%d",
			stats.TotalFailures, failureCount)
	}

	if totalProcessed+blockedCount != int64(totalRequests) {
		t.Errorf("Request accounting error: processed=%d, blocked=%d, total=%d",
			totalProcessed, blockedCount, totalRequests)
	}
}

// TestStateChangeCallback verifies callback is invoked on state transitions
func TestStateChangeCallback(t *testing.T) {
	var (
		mu          sync.Mutex
		transitions []string
	)

	config := Config{
		Name:                  "callback-test",
		FailureThreshold:      2,
		SuccessThreshold:      2,
		Timeout:               50 * time.Millisecond,
		MaxConcurrentRequests: 1,
		OnStateChange: func(from, to State) {
			mu.Lock()
			defer mu.Unlock()
			transitions = append(transitions, fmt.Sprintf("%s -> %s", from, to))
		},
	}

	cb, err := NewCircuitBreaker("callback-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Trigger state changes
	failFn := func() error { return errors.New("fail") }
	successFn := func() error { return nil }

	// Closed -> Open
	cb.Execute(failFn)
	cb.Execute(failFn)

	// Wait for timeout, then Open -> HalfOpen -> Closed
	time.Sleep(100 * time.Millisecond)
	cb.Execute(successFn)
	cb.Execute(successFn)

	time.Sleep(50 * time.Millisecond) // Allow callbacks to complete

	mu.Lock()
	defer mu.Unlock()

	if len(transitions) == 0 {
		t.Error("No state transitions recorded")
	}

	t.Logf("Transitions: %v", transitions)

	// Should have at least Closed->Open
	found := false
	for _, trans := range transitions {
		if trans == "CLOSED -> OPEN" {
			found = true
			break
		}
	}
	if !found {
		t.Error("Expected to find 'CLOSED -> OPEN' transition")
	}
}

// TestExecuteWithContext verifies context support
func TestExecuteWithContext(t *testing.T) {
	config := DefaultConfig("context-test")
	cb, err := NewCircuitBreaker("context-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Test with valid context
	ctx := context.Background()
	executed := false

	err = cb.ExecuteWithContext(ctx, func(ctx context.Context) error {
		executed = true
		return nil
	})

	if err != nil {
		t.Errorf("Expected successful execution, got error: %v", err)
	}
	if !executed {
		t.Error("Function was not executed")
	}

	// Test with cancelled context
	cancelCtx, cancel := context.WithCancel(context.Background())
	cancel()

	err = cb.ExecuteWithContext(cancelCtx, func(ctx context.Context) error {
		return ctx.Err()
	})

	if err == nil {
		t.Error("Expected error from cancelled context")
	}
}

// TestConfigValidation verifies configuration validation
func TestConfigValidation(t *testing.T) {
	tests := []struct {
		name        string
		config      Config
		expectError bool
	}{
		{
			name: "Valid config",
			config: Config{
				Name:                  "valid",
				FailureThreshold:      5,
				SuccessThreshold:      2,
				Timeout:               30 * time.Second,
				MaxConcurrentRequests: 1,
			},
			expectError: false,
		},
		{
			name: "Missing name",
			config: Config{
				Name:                  "",
				FailureThreshold:      5,
				SuccessThreshold:      2,
				Timeout:               30 * time.Second,
				MaxConcurrentRequests: 1,
			},
			expectError: true,
		},
		{
			name: "Zero failure threshold",
			config: Config{
				Name:                  "test",
				FailureThreshold:      0,
				SuccessThreshold:      2,
				Timeout:               30 * time.Second,
				MaxConcurrentRequests: 1,
			},
			expectError: true,
		},
		{
			name: "Zero success threshold",
			config: Config{
				Name:                  "test",
				FailureThreshold:      5,
				SuccessThreshold:      0,
				Timeout:               30 * time.Second,
				MaxConcurrentRequests: 1,
			},
			expectError: true,
		},
		{
			name: "Negative timeout",
			config: Config{
				Name:                  "test",
				FailureThreshold:      5,
				SuccessThreshold:      2,
				Timeout:               -1 * time.Second,
				MaxConcurrentRequests: 1,
			},
			expectError: true,
		},
		{
			name: "Zero max concurrent requests",
			config: Config{
				Name:                  "test",
				FailureThreshold:      5,
				SuccessThreshold:      2,
				Timeout:               30 * time.Second,
				MaxConcurrentRequests: 0,
			},
			expectError: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.expectError && err == nil {
				t.Error("Expected validation error, got nil")
			}
			if !tt.expectError && err != nil {
				t.Errorf("Expected no error, got: %v", err)
			}
		})
	}
}

// TestReset verifies reset functionality
func TestReset(t *testing.T) {
	config := Config{
		Name:                  "reset-test",
		FailureThreshold:      2,
		SuccessThreshold:      2,
		Timeout:               100 * time.Millisecond,
		MaxConcurrentRequests: 1,
	}

	cb, err := NewCircuitBreaker("reset-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Generate some activity
	failFn := func() error { return errors.New("fail") }
	cb.Execute(failFn)
	cb.Execute(failFn)

	if cb.GetState() != StateOpen {
		t.Fatalf("Expected state OPEN, got %v", cb.GetState())
	}

	// Reset
	cb.Reset()

	// Verify clean state
	state := cb.GetState()
	if state != StateClosed {
		t.Errorf("Expected state CLOSED after reset, got %v", state)
	}

	stats := cb.GetStats()
	if stats.TotalRequests != 0 {
		t.Errorf("Expected 0 total requests after reset, got %d", stats.TotalRequests)
	}
	if stats.TotalSuccesses != 0 {
		t.Errorf("Expected 0 successes after reset, got %d", stats.TotalSuccesses)
	}
	if stats.TotalFailures != 0 {
		t.Errorf("Expected 0 failures after reset, got %d", stats.TotalFailures)
	}
}

// TestSuccessRate verifies success rate calculation
func TestSuccessRate(t *testing.T) {
	config := DefaultConfig("rate-test")
	cb, err := NewCircuitBreaker("rate-test", config)
	if err != nil {
		t.Fatalf("Failed to create circuit breaker: %v", err)
	}

	// Execute mix of success/failure
	successFn := func() error { return nil }
	failFn := func() error { return errors.New("fail") }

	cb.Execute(successFn)
	cb.Execute(successFn)
	cb.Execute(successFn)
	cb.Execute(failFn)

	stats := cb.GetStats()
	rate := stats.SuccessRate()

	expectedRate := 0.75 // 3 successes out of 4 total
	if rate != expectedRate {
		t.Errorf("Expected success rate %.2f, got %.2f", expectedRate, rate)
	}
}

// BenchmarkCircuitBreakerClosed benchmarks performance in closed state
func BenchmarkCircuitBreakerClosed(b *testing.B) {
	config := DefaultConfig("bench-closed")
	cb, _ := NewCircuitBreaker("bench-closed", config)

	successFn := func() error { return nil }

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		cb.Execute(successFn)
	}
}

// BenchmarkCircuitBreakerOpen benchmarks performance in open state
func BenchmarkCircuitBreakerOpen(b *testing.B) {
	config := Config{
		Name:                  "bench-open",
		FailureThreshold:      2,
		SuccessThreshold:      2,
		Timeout:               1 * time.Hour, // Stay open
		MaxConcurrentRequests: 1,
	}
	cb, _ := NewCircuitBreaker("bench-open", config)

	// Open circuit
	failFn := func() error { return errors.New("fail") }
	cb.Execute(failFn)
	cb.Execute(failFn)

	successFn := func() error { return nil }

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		cb.Execute(successFn)
	}
}

// BenchmarkCircuitBreakerConcurrent benchmarks concurrent access
func BenchmarkCircuitBreakerConcurrent(b *testing.B) {
	config := DefaultConfig("bench-concurrent")
	cb, _ := NewCircuitBreaker("bench-concurrent", config)

	successFn := func() error { return nil }

	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			cb.Execute(successFn)
		}
	})
}
