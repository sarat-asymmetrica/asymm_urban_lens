package resilience

import (
	"context"
	"errors"
	"testing"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// BASIC TIMEOUT TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestWithTimeout_Success(t *testing.T) {
	ctx := context.Background()
	executed := false

	err := WithTimeout(ctx, 100*time.Millisecond, func() error {
		executed = true
		return nil
	})

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if !executed {
		t.Error("Function was not executed")
	}
}

func TestWithTimeout_Error(t *testing.T) {
	ctx := context.Background()
	testErr := errors.New("test error")

	err := WithTimeout(ctx, 100*time.Millisecond, func() error {
		return testErr
	})

	if err != testErr {
		t.Errorf("Expected %v, got %v", testErr, err)
	}
}

func TestWithTimeout_Timeout(t *testing.T) {
	ctx := context.Background()

	err := WithTimeout(ctx, 50*time.Millisecond, func() error {
		// Simulate slow operation
		time.Sleep(200 * time.Millisecond)
		return nil
	})

	if !errors.Is(err, ErrTimeout) {
		t.Errorf("Expected ErrTimeout, got %v", err)
	}
}

func TestWithTimeout_ContextCancellation(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())

	// Cancel immediately
	cancel()

	err := WithTimeout(ctx, 100*time.Millisecond, func() error {
		time.Sleep(50 * time.Millisecond)
		return nil
	})

	if err == nil {
		t.Error("Expected context cancellation error")
	}
}

func TestWithTimeout_Panic(t *testing.T) {
	ctx := context.Background()

	err := WithTimeout(ctx, 100*time.Millisecond, func() error {
		panic("test panic")
	})

	if err == nil {
		t.Error("Expected error from panic recovery")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// GENERIC RESULT TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestWithTimeoutResult_Success(t *testing.T) {
	ctx := context.Background()

	result, err := WithTimeoutResult(ctx, 100*time.Millisecond, func() (string, error) {
		return "success", nil
	})

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if result != "success" {
		t.Errorf("Expected 'success', got '%s'", result)
	}
}

func TestWithTimeoutResult_Error(t *testing.T) {
	ctx := context.Background()
	testErr := errors.New("test error")

	result, err := WithTimeoutResult(ctx, 100*time.Millisecond, func() (int, error) {
		return 0, testErr
	})

	if err != testErr {
		t.Errorf("Expected %v, got %v", testErr, err)
	}
	if result != 0 {
		t.Errorf("Expected zero value, got %d", result)
	}
}

func TestWithTimeoutResult_Timeout(t *testing.T) {
	ctx := context.Background()

	result, err := WithTimeoutResult(ctx, 50*time.Millisecond, func() (string, error) {
		time.Sleep(200 * time.Millisecond)
		return "too late", nil
	})

	if !errors.Is(err, ErrTimeout) {
		t.Errorf("Expected ErrTimeout, got %v", err)
	}
	if result != "" {
		t.Errorf("Expected zero value, got '%s'", result)
	}
}

func TestWithTimeoutResult_Panic(t *testing.T) {
	ctx := context.Background()

	result, err := WithTimeoutResult(ctx, 100*time.Millisecond, func() (bool, error) {
		panic("test panic")
	})

	if err == nil {
		t.Error("Expected error from panic recovery")
	}
	if result != false {
		t.Errorf("Expected zero value (false), got %v", result)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVENIENCE WRAPPER TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestWithAPITimeout_Success(t *testing.T) {
	ctx := context.Background()
	executed := false

	err := WithAPITimeout(ctx, func() error {
		executed = true
		return nil
	})

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if !executed {
		t.Error("Function was not executed")
	}
}

func TestWithCognitionTimeout_Success(t *testing.T) {
	ctx := context.Background()

	result, err := WithCognitionTimeoutResult(ctx, func() (int, error) {
		return 42, nil
	})

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if result != 42 {
		t.Errorf("Expected 42, got %d", result)
	}
}

func TestWithWebSocketTimeout_Success(t *testing.T) {
	ctx := context.Background()
	executed := false

	err := WithWebSocketTimeout(ctx, func() error {
		executed = true
		return nil
	})

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if !executed {
		t.Error("Function was not executed")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// RETRY TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestRetryWithTimeout_Success(t *testing.T) {
	ctx := context.Background()
	attempts := 0

	err := RetryWithTimeout(
		ctx,
		3,                     // maxRetries
		10*time.Millisecond,   // initialBackoff
		100*time.Millisecond,  // maxBackoff
		50*time.Millisecond,   // timeout
		func() error {
			attempts++
			return nil
		},
	)

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if attempts != 1 {
		t.Errorf("Expected 1 attempt, got %d", attempts)
	}
}

func TestRetryWithTimeout_SuccessAfterRetry(t *testing.T) {
	ctx := context.Background()
	attempts := 0

	err := RetryWithTimeout(
		ctx,
		3,                     // maxRetries
		10*time.Millisecond,   // initialBackoff
		100*time.Millisecond,  // maxBackoff
		50*time.Millisecond,   // timeout
		func() error {
			attempts++
			if attempts < 3 {
				return errors.New("temporary error")
			}
			return nil
		},
	)

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if attempts != 3 {
		t.Errorf("Expected 3 attempts, got %d", attempts)
	}
}

func TestRetryWithTimeout_MaxRetriesExceeded(t *testing.T) {
	ctx := context.Background()
	attempts := 0
	testErr := errors.New("persistent error")

	err := RetryWithTimeout(
		ctx,
		3,                     // maxRetries
		10*time.Millisecond,   // initialBackoff
		100*time.Millisecond,  // maxBackoff
		50*time.Millisecond,   // timeout
		func() error {
			attempts++
			return testErr
		},
	)

	if err != testErr {
		t.Errorf("Expected %v, got %v", testErr, err)
	}
	if attempts != 4 { // Initial + 3 retries
		t.Errorf("Expected 4 attempts, got %d", attempts)
	}
}

func TestRetryWithTimeoutResult_Success(t *testing.T) {
	ctx := context.Background()
	attempts := 0

	result, err := RetryWithTimeoutResult(
		ctx,
		3,                     // maxRetries
		10*time.Millisecond,   // initialBackoff
		100*time.Millisecond,  // maxBackoff
		50*time.Millisecond,   // timeout
		func() (string, error) {
			attempts++
			if attempts < 2 {
				return "", errors.New("temporary error")
			}
			return "success", nil
		},
	)

	if err != nil {
		t.Errorf("Expected no error, got %v", err)
	}
	if result != "success" {
		t.Errorf("Expected 'success', got '%s'", result)
	}
	if attempts != 2 {
		t.Errorf("Expected 2 attempts, got %d", attempts)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// BENCHMARK TESTS
// ═══════════════════════════════════════════════════════════════════════════

func BenchmarkWithTimeout_Success(b *testing.B) {
	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = WithTimeout(ctx, 100*time.Millisecond, func() error {
			return nil
		})
	}
}

func BenchmarkWithTimeoutResult_Success(b *testing.B) {
	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = WithTimeoutResult(ctx, 100*time.Millisecond, func() (int, error) {
			return 42, nil
		})
	}
}

func BenchmarkRetryWithTimeout_ImmediateSuccess(b *testing.B) {
	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = RetryWithTimeout(
			ctx,
			3,
			10*time.Millisecond,
			100*time.Millisecond,
			50*time.Millisecond,
			func() error {
				return nil
			},
		)
	}
}
