package intelligence

import (
	"context"
	"errors"
	"testing"
	"time"
)

// Test constants match research validation thresholds
const (
	VarianceThresholdMs = 50.0 // < 50ms variance proves determinism
	TimeoutMs           = 5000 // 5 second test timeout
)

// TestNewHarmonicTimer validates timer initialization
func TestNewHarmonicTimer(t *testing.T) {
	timer := NewHarmonicTimer()

	if timer == nil {
		t.Fatal("NewHarmonicTimer returned nil")
	}

	if timer.baseFrequency != TeslaFrequencyHz {
		t.Errorf("Expected frequency %.3f, got %.3f", TeslaFrequencyHz, timer.baseFrequency)
	}

	expectedPeriod := 204 * time.Millisecond // BasePeriodMs rounded
	if timer.basePeriod != expectedPeriod {
		t.Errorf("Expected period %v, got %v", expectedPeriod, timer.basePeriod)
	}
}

// TestCalculateDelay validates harmonic delay calculation
func TestCalculateDelay(t *testing.T) {
	timer := NewHarmonicTimer()

	tests := []struct {
		name     string
		multiple float64
		expectedMs float64
	}{
		{"1x harmonic", 1.0, BasePeriodMs},
		{"2x harmonic", 2.0, BasePeriodMs * 2},
		{"4x harmonic", 4.0, BasePeriodMs * 4},
		{"8x harmonic", 8.0, BasePeriodMs * 8},
		{"Zero", 0.0, 0.0},
		{"Negative (clamped)", -1.0, 0.0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			delay := timer.CalculateDelay(tt.multiple)
			actualMs := float64(delay.Milliseconds())

			// Allow small floating-point error (< 1ms)
			variance := actualMs - tt.expectedMs
			if variance < 0 {
				variance = -variance
			}

			if variance > 1.0 {
				t.Errorf("Expected ~%.2fms, got %.2fms (variance: %.2fms)",
					tt.expectedMs, actualMs, variance)
			}
		})
	}
}

// TestRetryWithBackoff validates exponential backoff with harmonic timing
func TestRetryWithBackoff(t *testing.T) {
	timer := NewHarmonicTimer()

	t.Run("Success on first attempt", func(t *testing.T) {
		attempts := 0
		operation := func() (interface{}, error) {
			attempts++
			return "success", nil
		}

		start := time.Now()
		result, err := timer.RetryWithBackoff(operation, 5)
		duration := time.Since(start)

		if err != nil {
			t.Errorf("Expected success, got error: %v", err)
		}

		if !result.Success {
			t.Error("Expected Success=true")
		}

		if result.Attempts != 1 {
			t.Errorf("Expected 1 attempt, got %d", result.Attempts)
		}

		if attempts != 1 {
			t.Errorf("Operation called %d times, expected 1", attempts)
		}

		// Should complete almost immediately (< 100ms)
		if duration > 100*time.Millisecond {
			t.Errorf("Duration %v too long for immediate success", duration)
		}
	})

	t.Run("Success on third attempt", func(t *testing.T) {
		attempts := 0
		operation := func() (interface{}, error) {
			attempts++
			if attempts < 3 {
				return nil, errors.New("not ready")
			}
			return "success", nil
		}

		start := time.Now()
		result, err := timer.RetryWithBackoff(operation, 5)
		duration := time.Since(start)

		if err != nil {
			t.Errorf("Expected success, got error: %v", err)
		}

		if !result.Success {
			t.Error("Expected Success=true")
		}

		if result.Attempts != 3 {
			t.Errorf("Expected 3 attempts, got %d", result.Attempts)
		}

		// Should wait: 1× + 2× harmonics
		// 1×203.7ms + 2×203.7ms = 611.1ms
		expectedMinMs := (BackoffSequence[0] + BackoffSequence[1]) * BasePeriodMs
		actualMs := float64(duration.Milliseconds())

		if actualMs < expectedMinMs-VarianceThresholdMs {
			t.Errorf("Duration %.2fms too short (expected ≥ %.2fms)",
				actualMs, expectedMinMs)
		}

		// Allow some overhead (< 200ms)
		if actualMs > expectedMinMs+200 {
			t.Errorf("Duration %.2fms too long (expected ~%.2fms)",
				actualMs, expectedMinMs)
		}
	})

	t.Run("All attempts fail", func(t *testing.T) {
		attempts := 0
		operation := func() (interface{}, error) {
			attempts++
			return nil, errors.New("always fails")
		}

		result, err := timer.RetryWithBackoff(operation, 3)

		if err == nil {
			t.Error("Expected error for all failures")
		}

		if result.Success {
			t.Error("Expected Success=false")
		}

		if result.Attempts != 3 {
			t.Errorf("Expected 3 attempts, got %d", result.Attempts)
		}

		if len(result.Errors) != 3 {
			t.Errorf("Expected 3 errors recorded, got %d", len(result.Errors))
		}
	})
}

// TestRetryWithBackoffContext validates context cancellation
func TestRetryWithBackoffContext(t *testing.T) {
	timer := NewHarmonicTimer()

	t.Run("Context timeout", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), 300*time.Millisecond)
		defer cancel()

		attempts := 0
		operation := func(ctx context.Context) (interface{}, error) {
			attempts++
			// Always fail to trigger retries
			return nil, errors.New("operation failed")
		}

		result, err := timer.RetryWithBackoffContext(ctx, operation, 5)

		// Should timeout during retries
		if err == nil {
			t.Error("Expected error due to timeout or operation failure")
		}

		if result.Success {
			t.Error("Expected Success=false")
		}

		// Should timeout before completing all 5 attempts
		// With backoff: 0ms + 204ms + 408ms = 612ms total
		// Timeout: 300ms, so should complete 1-2 attempts
		if result.Attempts >= 5 {
			t.Errorf("Expected < 5 attempts due to timeout, got %d", result.Attempts)
		}
	})

	t.Run("Context cancellation", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())

		attempts := 0
		operation := func(ctx context.Context) (interface{}, error) {
			attempts++
			if attempts == 1 {
				cancel() // Cancel after first attempt
			}
			return nil, errors.New("fail")
		}

		result, err := timer.RetryWithBackoffContext(ctx, operation, 5)

		if err != context.Canceled {
			t.Errorf("Expected Canceled, got: %v", err)
		}

		if result.Success {
			t.Error("Expected Success=false")
		}
	})
}

// TestRateLimit validates rate limiting calculation
func TestRateLimit(t *testing.T) {
	timer := NewHarmonicTimer()

	tests := []struct {
		name           string
		requestsPerSec float64
		expectedMs     float64
	}{
		{"5 req/sec (1× harmonic)", 5.0, BasePeriodMs},
		{"2.45 req/sec (2× harmonic)", 2.45, BasePeriodMs * 2},
		{"1 req/sec (5× harmonic)", 1.0, BasePeriodMs * 4.909},
		{"Zero (no limit)", 0.0, 0.0},
		{"Negative (no limit)", -1.0, 0.0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			delay := timer.RateLimit(tt.requestsPerSec)
			actualMs := float64(delay.Milliseconds())

			variance := actualMs - tt.expectedMs
			if variance < 0 {
				variance = -variance
			}

			// Allow small variance
			if variance > 5.0 {
				t.Errorf("Expected ~%.2fms, got %.2fms (variance: %.2fms)",
					tt.expectedMs, actualMs, variance)
			}
		})
	}
}

// TestSleepHarmonic validates harmonic sleep
func TestSleepHarmonic(t *testing.T) {
	timer := NewHarmonicTimer()

	t.Run("1 period sleep", func(t *testing.T) {
		start := time.Now()
		timer.SleepHarmonic(1)
		duration := time.Since(start)

		actualMs := float64(duration.Milliseconds())
		expectedMs := BasePeriodMs

		variance := CalculateTimingVariance(expectedMs, actualMs)

		if !IsWithinVarianceThreshold(expectedMs, actualMs, VarianceThresholdMs) {
			t.Errorf("Timing variance %.2fms exceeds threshold %.2fms",
				variance, VarianceThresholdMs)
		}
	})

	t.Run("Zero periods (no sleep)", func(t *testing.T) {
		start := time.Now()
		timer.SleepHarmonic(0)
		duration := time.Since(start)

		if duration > 10*time.Millisecond {
			t.Errorf("Expected no sleep, took %v", duration)
		}
	})
}

// TestSleepHarmonicContext validates context-aware sleep
func TestSleepHarmonicContext(t *testing.T) {
	timer := NewHarmonicTimer()

	t.Run("Normal sleep completes", func(t *testing.T) {
		ctx := context.Background()
		start := time.Now()
		err := timer.SleepHarmonicContext(ctx, 1)
		duration := time.Since(start)

		if err != nil {
			t.Errorf("Expected no error, got: %v", err)
		}

		actualMs := float64(duration.Milliseconds())
		expectedMs := BasePeriodMs

		variance := CalculateTimingVariance(expectedMs, actualMs)

		if variance > VarianceThresholdMs {
			t.Errorf("Timing variance %.2fms exceeds threshold", variance)
		}
	})

	t.Run("Context cancelled during sleep", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())

		// Cancel after 50ms
		go func() {
			time.Sleep(50 * time.Millisecond)
			cancel()
		}()

		start := time.Now()
		err := timer.SleepHarmonicContext(ctx, 5) // Would sleep ~1018.5ms
		duration := time.Since(start)

		if err != context.Canceled {
			t.Errorf("Expected Canceled, got: %v", err)
		}

		// Should cancel quickly (< 200ms)
		if duration > 200*time.Millisecond {
			t.Errorf("Expected quick cancellation, took %v", duration)
		}
	})
}

// TestTimingVariance validates variance calculation
func TestTimingVariance(t *testing.T) {
	tests := []struct {
		name       string
		expected   float64
		actual     float64
		variance   float64
		withinThreshold bool
	}{
		{"Exact match", 100.0, 100.0, 0.0, true},
		{"Small variance", 100.0, 110.0, 10.0, true},
		{"At threshold", 100.0, 150.0, 50.0, true},
		{"Exceeds threshold", 100.0, 160.0, 60.0, false},
		{"Negative difference", 100.0, 60.0, 40.0, true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			variance := CalculateTimingVariance(tt.expected, tt.actual)

			if variance != tt.variance {
				t.Errorf("Expected variance %.2f, got %.2f", tt.variance, variance)
			}

			withinThreshold := IsWithinVarianceThreshold(tt.expected, tt.actual, VarianceThresholdMs)

			if withinThreshold != tt.withinThreshold {
				t.Errorf("Expected withinThreshold=%v, got %v", tt.withinThreshold, withinThreshold)
			}
		})
	}
}

// TestBackoffSequence validates exponential backoff multipliers
func TestBackoffSequence(t *testing.T) {
	expected := []float64{1, 2, 4, 8, 16, 32, 64}

	if len(BackoffSequence) != len(expected) {
		t.Errorf("Expected %d elements, got %d", len(expected), len(BackoffSequence))
	}

	for i, mult := range expected {
		if i >= len(BackoffSequence) {
			break
		}

		if BackoffSequence[i] != mult {
			t.Errorf("BackoffSequence[%d]: expected %.0f, got %.0f",
				i, mult, BackoffSequence[i])
		}
	}
}

// TestTeslaConstants validates Tesla frequency constants
func TestTeslaConstants(t *testing.T) {
	// Tesla harmonic mean: H = 3 / (1/3 + 1/6 + 1/9) = 4.909...
	if TeslaFrequencyHz != 4.909 {
		t.Errorf("Expected TeslaFrequencyHz=4.909, got %.3f", TeslaFrequencyHz)
	}

	// Base period: 1/4.909 ≈ 0.2037s = 203.7ms
	expectedPeriodMs := 1.0 / TeslaFrequencyHz * 1000.0
	variance := BasePeriodMs - expectedPeriodMs
	if variance < 0 {
		variance = -variance
	}

	if variance > 0.1 {
		t.Errorf("BasePeriodMs %.3f doesn't match calculated %.3f",
			BasePeriodMs, expectedPeriodMs)
	}
}

// BenchmarkRetryWithBackoff benchmarks retry performance
func BenchmarkRetryWithBackoff(b *testing.B) {
	timer := NewHarmonicTimer()

	operation := func() (interface{}, error) {
		return "success", nil
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = timer.RetryWithBackoff(operation, 1)
	}
}

// BenchmarkCalculateDelay benchmarks delay calculation
func BenchmarkCalculateDelay(b *testing.B) {
	timer := NewHarmonicTimer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = timer.CalculateDelay(4.0)
	}
}
