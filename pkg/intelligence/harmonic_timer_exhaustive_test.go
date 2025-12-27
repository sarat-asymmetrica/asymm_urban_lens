package intelligence

import (
	"context"
	"errors"
	"math"
	"sync"
	"testing"
	"time"
)

// EXHAUSTIVE TEST SUITE FOR TESLA HARMONIC TIMER
//
// Mathematical Foundation (Commander's Research Paper):
// - Tesla Frequency: 4.909 Hz (harmonic mean of [3, 6, 9] Hz)
// - Base Period: 1/4.909 ≈ 0.2037 seconds (203.7 ms)
// - Harmonic delay: n × BASE_PERIOD_SECONDS
// - Backoff sequence: [1×T, 2×T, 4×T, 8×T, 16×T, ...] (exponential)
//
// Harmonic Mean Derivation:
//   H = 3 / (1/3 + 1/6 + 1/9)
//   H = 3 / (0.3333... + 0.1666... + 0.1111...)
//   H = 3 / 0.6111...
//   H ≈ 4.909 Hz
//
// Test Categories:
// 1. STABILIZATION (100% pass required): Core constants, mathematical foundations
// 2. OPTIMIZATION (85% pass required): Performance, variance, determinism
// 3. EXPLORATION (70% pass required): Integration, concurrency, edge cases
//
// Created: 2025-12-27 (Wave 1, Agent 3)
// Author: Zen Gardener (Claude)
// Mission: Exhaustive validation of Tesla Harmonic Timer

// =============================================================================
// STABILIZATION TESTS (100% REQUIRED)
// =============================================================================

// TestTeslaFrequency_Constant validates the Tesla frequency constant
//
// Mathematical Foundation:
//   Tesla electromagnetic resonance: 3, 6, 9 Hz harmonics
//   Harmonic mean: H = n / (Σ 1/xi) where n=3, x=[3,6,9]
//   H = 3 / (1/3 + 1/6 + 1/9) = 4.909 Hz
func TestTeslaFrequency_Constant(t *testing.T) {
	// Expected: 4.909 Hz exactly (from research paper)
	expected := 4.909

	if TeslaFrequencyHz != expected {
		t.Errorf("TeslaFrequencyHz = %.6f, expected %.6f", TeslaFrequencyHz, expected)
	}

	// Verify it's positive and reasonable
	if TeslaFrequencyHz <= 0 {
		t.Error("TeslaFrequencyHz must be positive")
	}

	if TeslaFrequencyHz < 3.0 || TeslaFrequencyHz > 10.0 {
		t.Errorf("TeslaFrequencyHz %.3f outside reasonable range [3, 10] Hz", TeslaFrequencyHz)
	}
}

// TestBasePeriod_Calculation validates base period calculation
//
// Mathematical Foundation:
//   Period = 1 / Frequency
//   BasePeriodMs = 1 / 4.909 × 1000 = 203.7 ms
func TestBasePeriod_Calculation(t *testing.T) {
	// Calculate expected period from frequency
	expectedMs := 1.0 / TeslaFrequencyHz * 1000.0 // ≈ 203.7 ms

	// Allow tiny floating-point error
	variance := math.Abs(BasePeriodMs - expectedMs)
	if variance > 0.5 {
		t.Errorf("BasePeriodMs = %.3f, expected %.3f (variance: %.3fms)",
			BasePeriodMs, expectedMs, variance)
	}

	// Verify BasePeriod duration is consistent
	// Allow 1ms rounding tolerance
	actualMs := float64(BasePeriod.Milliseconds())
	periodVariance := math.Abs(actualMs - BasePeriodMs)
	if periodVariance > 1.0 {
		t.Errorf("BasePeriod = %v (%.2fms), expected ~%.2fms (variance: %.2fms)",
			BasePeriod, actualMs, BasePeriodMs, periodVariance)
	}

	t.Logf("✓ BasePeriod validated: %.3f ms (from 1/%.3f Hz)", BasePeriodMs, TeslaFrequencyHz)
}

// TestHarmonicDelay_1x validates 1× harmonic delay
//
// Formula: delay = 1 × BASE_PERIOD = 203.7 ms
func TestHarmonicDelay_1x(t *testing.T) {
	timer := NewHarmonicTimer()
	delay := timer.CalculateDelay(1.0)

	expectedMs := BasePeriodMs // 1× = 203.7 ms
	actualMs := float64(delay.Milliseconds())

	variance := math.Abs(actualMs - expectedMs)
	if variance > 1.0 {
		t.Errorf("1× harmonic delay = %.2fms, expected %.2fms (variance: %.2fms)",
			actualMs, expectedMs, variance)
	}

	t.Logf("✓ 1× harmonic delay: %.2f ms", actualMs)
}

// TestHarmonicDelay_2x validates 2× harmonic delay
//
// Formula: delay = 2 × BASE_PERIOD = 407.4 ms
func TestHarmonicDelay_2x(t *testing.T) {
	timer := NewHarmonicTimer()
	delay := timer.CalculateDelay(2.0)

	expectedMs := BasePeriodMs * 2.0 // 2× = 407.4 ms
	actualMs := float64(delay.Milliseconds())

	variance := math.Abs(actualMs - expectedMs)
	if variance > 2.0 {
		t.Errorf("2× harmonic delay = %.2fms, expected %.2fms (variance: %.2fms)",
			actualMs, expectedMs, variance)
	}

	t.Logf("✓ 2× harmonic delay: %.2f ms", actualMs)
}

// TestHarmonicDelay_4x validates 4× harmonic delay
//
// Formula: delay = 4 × BASE_PERIOD = 814.8 ms
func TestHarmonicDelay_4x(t *testing.T) {
	timer := NewHarmonicTimer()
	delay := timer.CalculateDelay(4.0)

	expectedMs := BasePeriodMs * 4.0 // 4× = 814.8 ms
	actualMs := float64(delay.Milliseconds())

	variance := math.Abs(actualMs - expectedMs)
	if variance > 3.0 {
		t.Errorf("4× harmonic delay = %.2fms, expected %.2fms (variance: %.2fms)",
			actualMs, expectedMs, variance)
	}

	t.Logf("✓ 4× harmonic delay: %.2f ms", actualMs)
}

// TestHarmonicDelay_8x validates 8× harmonic delay
//
// Formula: delay = 8 × BASE_PERIOD = 1629.6 ms
func TestHarmonicDelay_8x(t *testing.T) {
	timer := NewHarmonicTimer()
	delay := timer.CalculateDelay(8.0)

	expectedMs := BasePeriodMs * 8.0 // 8× = 1629.6 ms
	actualMs := float64(delay.Milliseconds())

	variance := math.Abs(actualMs - expectedMs)
	if variance > 5.0 {
		t.Errorf("8× harmonic delay = %.2fms, expected %.2fms (variance: %.2fms)",
			actualMs, expectedMs, variance)
	}

	t.Logf("✓ 8× harmonic delay: %.2f ms", actualMs)
}

// TestHarmonicDelay_16x validates 16× harmonic delay
//
// Formula: delay = 16 × BASE_PERIOD = 3259.2 ms
func TestHarmonicDelay_16x(t *testing.T) {
	timer := NewHarmonicTimer()
	delay := timer.CalculateDelay(16.0)

	expectedMs := BasePeriodMs * 16.0 // 16× = 3259.2 ms
	actualMs := float64(delay.Milliseconds())

	variance := math.Abs(actualMs - expectedMs)
	if variance > 10.0 {
		t.Errorf("16× harmonic delay = %.2fms, expected %.2fms (variance: %.2fms)",
			actualMs, expectedMs, variance)
	}

	t.Logf("✓ 16× harmonic delay: %.2f ms", actualMs)
}

// TestHarmonicMean_Derivation validates harmonic mean calculation
//
// Mathematical Proof:
//   Given: frequencies [3, 6, 9] Hz
//   Harmonic Mean: H = n / (Σ 1/xi)
//   H = 3 / (1/3 + 1/6 + 1/9)
//   H = 3 / (0.33333... + 0.16666... + 0.11111...)
//   H = 3 / 0.61111...
//   H = 4.90909... ≈ 4.909 Hz
func TestHarmonicMean_Derivation(t *testing.T) {
	frequencies := []float64{3.0, 6.0, 9.0} // Tesla's 3-6-9 harmonics
	n := float64(len(frequencies))

	// Calculate harmonic mean: H = n / Σ(1/xi)
	sumReciprocals := 0.0
	for _, f := range frequencies {
		sumReciprocals += 1.0 / f
	}
	harmonicMean := n / sumReciprocals

	// Expected: 4.909 Hz
	expected := 4.909

	variance := math.Abs(harmonicMean - expected)
	if variance > 0.001 {
		t.Errorf("Harmonic mean = %.6f, expected %.6f (variance: %.6f)",
			harmonicMean, expected, variance)
	}

	// Verify TeslaFrequencyHz matches derivation
	if math.Abs(TeslaFrequencyHz-harmonicMean) > 0.001 {
		t.Errorf("TeslaFrequencyHz = %.6f doesn't match derived harmonic mean %.6f",
			TeslaFrequencyHz, harmonicMean)
	}

	t.Logf("✓ Harmonic mean derivation validated:")
	t.Logf("  Frequencies: %v Hz", frequencies)
	t.Logf("  Sum reciprocals: 1/3 + 1/6 + 1/9 = %.6f", sumReciprocals)
	t.Logf("  Harmonic mean: 3 / %.6f = %.6f Hz", sumReciprocals, harmonicMean)
}

// TestBackoffSequence_Exponential validates exponential backoff pattern
//
// Pattern: [1, 2, 4, 8, 16, 32, 64]
// Each element is 2× the previous (exponential growth)
func TestBackoffSequence_Exponential(t *testing.T) {
	expected := []float64{1, 2, 4, 8, 16, 32, 64}

	if len(BackoffSequence) != len(expected) {
		t.Errorf("BackoffSequence length = %d, expected %d",
			len(BackoffSequence), len(expected))
	}

	for i, expectedVal := range expected {
		if i >= len(BackoffSequence) {
			break
		}

		actualVal := BackoffSequence[i]
		if actualVal != expectedVal {
			t.Errorf("BackoffSequence[%d] = %.0f, expected %.0f",
				i, actualVal, expectedVal)
		}

		// Verify exponential relationship (each is 2× previous)
		if i > 0 {
			prevVal := BackoffSequence[i-1]
			ratio := actualVal / prevVal
			if math.Abs(ratio-2.0) > 0.001 {
				t.Errorf("BackoffSequence[%d]/[%d] = %.3f, expected 2.0 (exponential)",
					i, i-1, ratio)
			}
		}
	}

	t.Logf("✓ Exponential backoff sequence validated: %v", BackoffSequence)
}

// =============================================================================
// OPTIMIZATION TESTS (85% REQUIRED)
// =============================================================================

// TestTimingVariance_LessThan50ms validates deterministic timing
//
// Research Validation: < 50ms variance proves determinism
// (from Unified Intelligence Monitoring Research Paper, Day 142)
func TestTimingVariance_LessThan50ms(t *testing.T) {
	timer := NewHarmonicTimer()

	// Test multiple harmonic delays
	testCases := []struct {
		multiple   float64
		name       string
	}{
		{1.0, "1× harmonic"},
		{2.0, "2× harmonic"},
		{4.0, "4× harmonic"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			expectedMs := tc.multiple * BasePeriodMs

			// Measure actual sleep time
			start := time.Now()
			delay := timer.CalculateDelay(tc.multiple)
			time.Sleep(delay)
			actualMs := float64(time.Since(start).Milliseconds())

			variance := CalculateTimingVariance(expectedMs, actualMs)

			// Research validation threshold: 50ms
			if variance > 50.0 {
				t.Errorf("Timing variance %.2fms exceeds 50ms threshold (%.2f× harmonic)",
					variance, tc.multiple)
			}

			// Determinism proof: within system clock granularity
			if !IsWithinVarianceThreshold(expectedMs, actualMs, 50.0) {
				t.Errorf("Timing not deterministic: expected %.2fms, got %.2fms (variance: %.2fms)",
					expectedMs, actualMs, variance)
			}

			t.Logf("✓ %.1f× harmonic: expected %.2fms, actual %.2fms, variance %.2fms (< 50ms)",
				tc.multiple, expectedMs, actualMs, variance)
		})
	}
}

// TestRateLimiting_5RequestsPerSecond validates rate limiting accuracy
//
// At 1× harmonic (203.7ms delay), should achieve ~4.9 req/sec
// Formula: rate = 1 / delay = 1000ms / 203.7ms ≈ 4.909 req/sec
func TestRateLimiting_5RequestsPerSecond(t *testing.T) {
	timer := NewHarmonicTimer()

	// Calculate delay for 5 req/sec
	delay := timer.RateLimit(5.0)
	expectedMs := BasePeriodMs // 1× harmonic for ~4.9 req/sec

	actualMs := float64(delay.Milliseconds())
	variance := math.Abs(actualMs - expectedMs)

	if variance > 5.0 {
		t.Errorf("Rate limit delay = %.2fms, expected ~%.2fms (variance: %.2fms)",
			actualMs, expectedMs, variance)
	}

	// Verify actual rate achieved
	numRequests := 10
	start := time.Now()
	for i := 0; i < numRequests; i++ {
		time.Sleep(delay)
	}
	duration := time.Since(start)

	// Calculate requests per second
	actualRate := float64(numRequests) / duration.Seconds()
	expectedRate := 5.0

	rateVariance := math.Abs(actualRate - expectedRate)
	// Allow 20% variance due to system timing
	if rateVariance > expectedRate*0.2 {
		t.Errorf("Actual rate = %.2f req/sec, expected ~%.2f req/sec (variance: %.2f)",
			actualRate, expectedRate, rateVariance)
	}

	t.Logf("✓ Rate limiting: %.2f req/sec achieved (expected %.2f), delay %.2fms",
		actualRate, expectedRate, actualMs)
}

// TestBackoffRetry_Success validates retry succeeds on transient failure
//
// Simulates transient failure that resolves after N attempts
func TestBackoffRetry_Success(t *testing.T) {
	timer := NewHarmonicTimer()

	testCases := []struct {
		failUntilAttempt int
		name             string
	}{
		{1, "Success on first attempt"},
		{2, "Success on second attempt"},
		{3, "Success on third attempt"},
		{4, "Success on fourth attempt"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			attempts := 0
			operation := func() (interface{}, error) {
				attempts++
				if attempts < tc.failUntilAttempt {
					return nil, errors.New("transient failure")
				}
				return "success", nil
			}

			result, err := timer.RetryWithBackoff(operation, 5)

			if err != nil {
				t.Errorf("Expected success, got error: %v", err)
			}

			if !result.Success {
				t.Error("Expected Success=true")
			}

			if result.Attempts != tc.failUntilAttempt {
				t.Errorf("Expected %d attempts, got %d", tc.failUntilAttempt, result.Attempts)
			}

			t.Logf("✓ Retry succeeded after %d attempts (duration: %v)",
				result.Attempts, result.Duration)
		})
	}
}

// TestBackoffRetry_MaxAttempts validates failure after max attempts
//
// Verifies retry logic stops after maxAttempts reached
func TestBackoffRetry_MaxAttempts(t *testing.T) {
	timer := NewHarmonicTimer()

	testCases := []int{1, 3, 5, 10} // Different max attempts

	for _, maxAttempts := range testCases {
		t.Run(time.Duration(maxAttempts).String()+" max attempts", func(t *testing.T) {
			attempts := 0
			operation := func() (interface{}, error) {
				attempts++
				return nil, errors.New("persistent failure")
			}

			result, err := timer.RetryWithBackoff(operation, maxAttempts)

			if err == nil {
				t.Error("Expected error for persistent failure")
			}

			if result.Success {
				t.Error("Expected Success=false")
			}

			if result.Attempts != maxAttempts {
				t.Errorf("Expected %d attempts, got %d", maxAttempts, result.Attempts)
			}

			if len(result.Errors) != maxAttempts {
				t.Errorf("Expected %d errors recorded, got %d",
					maxAttempts, len(result.Errors))
			}

			t.Logf("✓ Failed after %d attempts as expected (duration: %v)",
				result.Attempts, result.Duration)
		})
	}
}

// =============================================================================
// EXPLORATION TESTS (70% REQUIRED)
// =============================================================================

// TestHarmonicTimer_Integration_WithContext validates context integration
//
// Tests:
// - Context timeout during retries
// - Context cancellation during retries
// - Context passed to operation
func TestHarmonicTimer_Integration_WithContext(t *testing.T) {
	timer := NewHarmonicTimer()

	t.Run("Timeout during backoff", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), 500*time.Millisecond)
		defer cancel()

		attempts := 0
		operation := func(ctx context.Context) (interface{}, error) {
			attempts++
			// Always fail to trigger max retries
			return nil, errors.New("fail")
		}

		start := time.Now()
		result, err := timer.RetryWithBackoffContext(ctx, operation, 10)
		duration := time.Since(start)

		// Should timeout before 10 attempts
		// Backoff: 0ms + 204ms + 408ms + 816ms = 1428ms (would exceed 500ms timeout)
		if err == nil {
			t.Error("Expected error (timeout or operation failure)")
		}

		if result.Attempts >= 10 {
			t.Errorf("Expected < 10 attempts due to timeout, got %d", result.Attempts)
		}

		// Should timeout around 500ms
		if duration > 700*time.Millisecond {
			t.Errorf("Duration %v exceeds timeout+margin (500ms+200ms)", duration)
		}

		t.Logf("✓ Context timeout: stopped after %d attempts in %v", result.Attempts, duration)
	})

	t.Run("Immediate cancellation", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())
		cancel() // Cancel immediately

		operation := func(ctx context.Context) (interface{}, error) {
			return nil, errors.New("should not execute")
		}

		result, err := timer.RetryWithBackoffContext(ctx, operation, 5)

		if err != context.Canceled {
			t.Errorf("Expected context.Canceled, got: %v", err)
		}

		if result.Success {
			t.Error("Expected Success=false")
		}

		t.Logf("✓ Immediate cancellation handled correctly")
	})

	t.Run("Context passed to operation", func(t *testing.T) {
		ctx := context.WithValue(context.Background(), "test-key", "test-value")

		ctxReceived := false
		operation := func(ctx context.Context) (interface{}, error) {
			// Verify context value is passed
			if val := ctx.Value("test-key"); val == "test-value" {
				ctxReceived = true
			}
			return "success", nil
		}

		result, err := timer.RetryWithBackoffContext(ctx, operation, 1)

		if err != nil {
			t.Errorf("Expected success, got error: %v", err)
		}

		if !ctxReceived {
			t.Error("Context not properly passed to operation")
		}

		if !result.Success {
			t.Error("Expected Success=true")
		}

		t.Logf("✓ Context properly passed to operation")
	})
}

// TestHarmonicTimer_Concurrent_Safety validates goroutine safety
//
// Tests:
// - Multiple goroutines using same timer
// - No data races
// - Deterministic behavior across threads
func TestHarmonicTimer_Concurrent_Safety(t *testing.T) {
	timer := NewHarmonicTimer()

	// Launch multiple goroutines using timer concurrently
	numGoroutines := 10
	var wg sync.WaitGroup
	wg.Add(numGoroutines)

	results := make(chan *RetryResult, numGoroutines)
	errors := make(chan error, numGoroutines)

	for i := 0; i < numGoroutines; i++ {
		go func(id int) {
			defer wg.Done()

			operation := func() (interface{}, error) {
				// Simulate work
				time.Sleep(10 * time.Millisecond)
				return id, nil
			}

			result, err := timer.RetryWithBackoff(operation, 3)
			results <- result
			errors <- err
		}(i)
	}

	wg.Wait()
	close(results)
	close(errors)

	// Validate all succeeded
	successCount := 0
	for result := range results {
		if result.Success {
			successCount++
		}
	}

	if successCount != numGoroutines {
		t.Errorf("Expected %d successes, got %d", numGoroutines, successCount)
	}

	errorCount := 0
	for err := range errors {
		if err != nil {
			errorCount++
		}
	}

	if errorCount > 0 {
		t.Errorf("Expected 0 errors, got %d", errorCount)
	}

	t.Logf("✓ Concurrent safety: %d goroutines completed successfully", numGoroutines)
}

// TestHarmonicTimer_EdgeCases validates edge case handling
//
// Tests:
// - Zero/negative delays
// - Very large multiples
// - Boundary conditions
func TestHarmonicTimer_EdgeCases(t *testing.T) {
	timer := NewHarmonicTimer()

	t.Run("Zero delay", func(t *testing.T) {
		delay := timer.CalculateDelay(0.0)
		if delay != 0 {
			t.Errorf("Expected 0 delay, got %v", delay)
		}
	})

	t.Run("Negative delay (clamped to zero)", func(t *testing.T) {
		delay := timer.CalculateDelay(-5.0)
		if delay != 0 {
			t.Errorf("Expected 0 delay (clamped), got %v", delay)
		}
	})

	t.Run("Very large multiple", func(t *testing.T) {
		delay := timer.CalculateDelay(1000.0)
		expectedMs := 1000.0 * BasePeriodMs // ~203,700 ms = ~203 seconds
		actualMs := float64(delay.Milliseconds())

		variance := math.Abs(actualMs - expectedMs)
		if variance > 10.0 {
			t.Errorf("Large delay: expected %.2fms, got %.2fms (variance: %.2fms)",
				expectedMs, actualMs, variance)
		}
	})

	t.Run("Fractional multiple", func(t *testing.T) {
		delay := timer.CalculateDelay(1.5)
		expectedMs := 1.5 * BasePeriodMs // ~305.55 ms
		actualMs := float64(delay.Milliseconds())

		variance := math.Abs(actualMs - expectedMs)
		if variance > 2.0 {
			t.Errorf("Fractional delay: expected %.2fms, got %.2fms (variance: %.2fms)",
				expectedMs, actualMs, variance)
		}
	})

	t.Run("Zero max attempts (uses default)", func(t *testing.T) {
		operation := func() (interface{}, error) {
			return "success", nil
		}

		result, err := timer.RetryWithBackoff(operation, 0)

		if err != nil {
			t.Errorf("Expected success with default attempts, got error: %v", err)
		}

		// Should default to 5 attempts max (though succeeds on first)
		if result.Attempts != 1 {
			t.Errorf("Expected 1 attempt (immediate success), got %d", result.Attempts)
		}
	})

	t.Run("Rate limit with zero/negative rate", func(t *testing.T) {
		delay := timer.RateLimit(0.0)
		if delay != 0 {
			t.Errorf("Expected 0 delay for zero rate, got %v", delay)
		}

		delay = timer.RateLimit(-1.0)
		if delay != 0 {
			t.Errorf("Expected 0 delay for negative rate, got %v", delay)
		}
	})

	t.Logf("✓ Edge cases handled correctly")
}

// TestHarmonicTimer_Getters validates getter methods
func TestHarmonicTimer_Getters(t *testing.T) {
	timer := NewHarmonicTimer()

	freq := timer.GetFrequency()
	if freq != TeslaFrequencyHz {
		t.Errorf("GetFrequency() = %.6f, expected %.6f", freq, TeslaFrequencyHz)
	}

	period := timer.GetBasePeriod()
	if period != BasePeriod {
		t.Errorf("GetBasePeriod() = %v, expected %v", period, BasePeriod)
	}

	t.Logf("✓ Getters validated: %.3f Hz, %v period", freq, period)
}

// =============================================================================
// BENCHMARKS (Performance Validation)
// =============================================================================

// BenchmarkHarmonicDelay_Calculation benchmarks delay calculation performance
func BenchmarkHarmonicDelay_Calculation(b *testing.B) {
	timer := NewHarmonicTimer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = timer.CalculateDelay(4.0)
	}
}

// BenchmarkRetryWithBackoff_Success benchmarks retry performance
func BenchmarkRetryWithBackoff_Success(b *testing.B) {
	timer := NewHarmonicTimer()

	operation := func() (interface{}, error) {
		return "success", nil
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = timer.RetryWithBackoff(operation, 1)
	}
}

// BenchmarkRateLimit_Calculation benchmarks rate limit calculation
func BenchmarkRateLimit_Calculation(b *testing.B) {
	timer := NewHarmonicTimer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = timer.RateLimit(5.0)
	}
}

// =============================================================================
// TESLA ELECTROMAGNETIC FOUNDATION VALIDATION
// =============================================================================

// TestTesla_369_Harmonics validates Tesla's 3-6-9 electromagnetic principle
//
// Quote: "If you only knew the magnificence of the 3, 6 and 9,
//         then you would have the key to the universe." - Nikola Tesla
func TestTesla_369_Harmonics(t *testing.T) {
	// Tesla's sacred frequencies
	teslaFrequencies := []float64{3.0, 6.0, 9.0}

	// Verify each is divisible by 3 (Tesla's observation)
	for _, f := range teslaFrequencies {
		if math.Mod(f, 3.0) != 0.0 {
			t.Errorf("Frequency %.1f not divisible by 3 (Tesla principle violated)", f)
		}
	}

	// Verify geometric relationship: 6 = 2×3, 9 = 3×3
	if teslaFrequencies[1] != teslaFrequencies[0]*2.0 {
		t.Error("6 Hz should be 2× 3 Hz")
	}
	if teslaFrequencies[2] != teslaFrequencies[0]*3.0 {
		t.Error("9 Hz should be 3× 3 Hz")
	}

	// Verify harmonic mean produces our base frequency
	n := float64(len(teslaFrequencies))
	sumReciprocals := 0.0
	for _, f := range teslaFrequencies {
		sumReciprocals += 1.0 / f
	}
	harmonicMean := n / sumReciprocals

	if math.Abs(harmonicMean-TeslaFrequencyHz) > 0.001 {
		t.Errorf("Harmonic mean %.6f doesn't match TeslaFrequencyHz %.6f",
			harmonicMean, TeslaFrequencyHz)
	}

	t.Logf("✓ Tesla 3-6-9 electromagnetic harmonics validated:")
	t.Logf("  Sacred frequencies: %v Hz", teslaFrequencies)
	t.Logf("  Harmonic mean: %.6f Hz (base timing frequency)", harmonicMean)
	t.Logf("  'If you only knew the magnificence of the 3, 6 and 9...' - Tesla")
}
