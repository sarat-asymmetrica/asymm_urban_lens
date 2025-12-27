// Package resilience provides timeout handling for all external calls
// Built with LOVE × SIMPLICITY × TRUTH × JOY 🕉️
//
// Features:
// - Context-based timeout wrappers
// - Clean resource cleanup
// - Generic support for any return type
// - Proper error handling
//
// Built on Asymmetrica Mathematical Organism foundations
package resilience

import (
	"context"
	"errors"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// ERRORS
// ═══════════════════════════════════════════════════════════════════════════

// ErrTimeout is returned when an operation times out
var ErrTimeout = errors.New("operation timed out")

// ═══════════════════════════════════════════════════════════════════════════
// TIMEOUT WRAPPERS
// ═══════════════════════════════════════════════════════════════════════════

// WithTimeout executes a function with a timeout
// Returns ErrTimeout if the timeout is exceeded
func WithTimeout(ctx context.Context, timeout time.Duration, fn func() error) error {
	// Create context with timeout
	timeoutCtx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	// Channel for result
	errChan := make(chan error, 1)

	// Execute function in goroutine
	go func() {
		defer func() {
			// Recover from panics and convert to error
			if r := recover(); r != nil {
				errChan <- errors.New("panic recovered")
			}
		}()
		errChan <- fn()
	}()

	// Wait for either completion or timeout
	select {
	case err := <-errChan:
		return err
	case <-timeoutCtx.Done():
		// Context cancelled or timed out
		if errors.Is(timeoutCtx.Err(), context.DeadlineExceeded) {
			return ErrTimeout
		}
		return timeoutCtx.Err()
	}
}

// WithTimeoutResult executes a function with a timeout and returns a result
// Generic function supporting any return type T
func WithTimeoutResult[T any](ctx context.Context, timeout time.Duration, fn func() (T, error)) (T, error) {
	// Create context with timeout
	timeoutCtx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	// Channel for result
	type result struct {
		value T
		err   error
	}
	resultChan := make(chan result, 1)

	// Execute function in goroutine
	go func() {
		defer func() {
			// Recover from panics and convert to error
			if r := recover(); r != nil {
				var zero T
				resultChan <- result{value: zero, err: errors.New("panic recovered")}
			}
		}()
		value, err := fn()
		resultChan <- result{value: value, err: err}
	}()

	// Wait for either completion or timeout
	select {
	case res := <-resultChan:
		return res.value, res.err
	case <-timeoutCtx.Done():
		// Context cancelled or timed out
		var zero T
		if errors.Is(timeoutCtx.Err(), context.DeadlineExceeded) {
			return zero, ErrTimeout
		}
		return zero, timeoutCtx.Err()
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// DEFAULT TIMEOUTS
// ═══════════════════════════════════════════════════════════════════════════

const (
	// DefaultAPITimeout is the default timeout for API calls (30 seconds)
	DefaultAPITimeout = 30 * time.Second

	// DefaultCognitionTimeout is the default timeout for cognition snapshots (5 seconds)
	DefaultCognitionTimeout = 5 * time.Second

	// DefaultWebSocketTimeout is the default timeout for WebSocket operations (10 seconds)
	DefaultWebSocketTimeout = 10 * time.Second

	// DefaultDatabaseTimeout is the default timeout for database operations (15 seconds)
	DefaultDatabaseTimeout = 15 * time.Second

	// DefaultStreamingTimeout is the default timeout for streaming operations (60 seconds)
	DefaultStreamingTimeout = 60 * time.Second
)

// ═══════════════════════════════════════════════════════════════════════════
// CONVENIENCE WRAPPERS
// ═══════════════════════════════════════════════════════════════════════════

// WithAPITimeout executes a function with API timeout (30s)
func WithAPITimeout(ctx context.Context, fn func() error) error {
	return WithTimeout(ctx, DefaultAPITimeout, fn)
}

// WithAPITimeoutResult executes a function with API timeout and returns a result
func WithAPITimeoutResult[T any](ctx context.Context, fn func() (T, error)) (T, error) {
	return WithTimeoutResult(ctx, DefaultAPITimeout, fn)
}

// WithCognitionTimeout executes a function with cognition timeout (5s)
func WithCognitionTimeout(ctx context.Context, fn func() error) error {
	return WithTimeout(ctx, DefaultCognitionTimeout, fn)
}

// WithCognitionTimeoutResult executes a function with cognition timeout and returns a result
func WithCognitionTimeoutResult[T any](ctx context.Context, fn func() (T, error)) (T, error) {
	return WithTimeoutResult(ctx, DefaultCognitionTimeout, fn)
}

// WithWebSocketTimeout executes a function with WebSocket timeout (10s)
func WithWebSocketTimeout(ctx context.Context, fn func() error) error {
	return WithTimeout(ctx, DefaultWebSocketTimeout, fn)
}

// WithWebSocketTimeoutResult executes a function with WebSocket timeout and returns a result
func WithWebSocketTimeoutResult[T any](ctx context.Context, fn func() (T, error)) (T, error) {
	return WithTimeoutResult(ctx, DefaultWebSocketTimeout, fn)
}

// WithDatabaseTimeout executes a function with database timeout (15s)
func WithDatabaseTimeout(ctx context.Context, fn func() error) error {
	return WithTimeout(ctx, DefaultDatabaseTimeout, fn)
}

// WithDatabaseTimeoutResult executes a function with database timeout and returns a result
func WithDatabaseTimeoutResult[T any](ctx context.Context, fn func() (T, error)) (T, error) {
	return WithTimeoutResult(ctx, DefaultDatabaseTimeout, fn)
}

// WithStreamingTimeout executes a function with streaming timeout (60s)
func WithStreamingTimeout(ctx context.Context, fn func() error) error {
	return WithTimeout(ctx, DefaultStreamingTimeout, fn)
}

// WithStreamingTimeoutResult executes a function with streaming timeout and returns a result
func WithStreamingTimeoutResult[T any](ctx context.Context, fn func() (T, error)) (T, error) {
	return WithTimeoutResult(ctx, DefaultStreamingTimeout, fn)
}

// ═══════════════════════════════════════════════════════════════════════════
// RETRY WITH TIMEOUT
// ═══════════════════════════════════════════════════════════════════════════

// RetryWithTimeout retries a function with exponential backoff and timeout
// maxRetries: maximum number of retry attempts
// initialBackoff: initial backoff duration
// maxBackoff: maximum backoff duration
// timeout: timeout for each individual attempt
func RetryWithTimeout(
	ctx context.Context,
	maxRetries int,
	initialBackoff time.Duration,
	maxBackoff time.Duration,
	timeout time.Duration,
	fn func() error,
) error {
	var lastErr error
	backoff := initialBackoff

	for attempt := 0; attempt <= maxRetries; attempt++ {
		// Execute with timeout
		err := WithTimeout(ctx, timeout, fn)
		if err == nil {
			return nil // Success!
		}

		lastErr = err

		// Check if we should retry
		if attempt < maxRetries {
			// Wait before retry
			select {
			case <-time.After(backoff):
				// Exponential backoff with jitter
				backoff *= 2
				if backoff > maxBackoff {
					backoff = maxBackoff
				}
			case <-ctx.Done():
				return ctx.Err()
			}
		}
	}

	return lastErr
}

// RetryWithTimeoutResult retries a function with exponential backoff and returns a result
func RetryWithTimeoutResult[T any](
	ctx context.Context,
	maxRetries int,
	initialBackoff time.Duration,
	maxBackoff time.Duration,
	timeout time.Duration,
	fn func() (T, error),
) (T, error) {
	var lastErr error
	var zero T
	backoff := initialBackoff

	for attempt := 0; attempt <= maxRetries; attempt++ {
		// Execute with timeout
		value, err := WithTimeoutResult(ctx, timeout, fn)
		if err == nil {
			return value, nil // Success!
		}

		lastErr = err

		// Check if we should retry
		if attempt < maxRetries {
			// Wait before retry
			select {
			case <-time.After(backoff):
				// Exponential backoff with jitter
				backoff *= 2
				if backoff > maxBackoff {
					backoff = maxBackoff
				}
			case <-ctx.Done():
				return zero, ctx.Err()
			}
		}
	}

	return zero, lastErr
}
