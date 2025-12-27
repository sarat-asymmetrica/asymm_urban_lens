# Resilience Package

**Production-ready fault-tolerance patterns for distributed systems**

> "Apollo landed because we handled errors." - Margaret Hamilton

## Overview

The `resilience` package provides battle-tested patterns to build reliable distributed systems:

- **Circuit Breaker**: Prevent cascading failures by failing fast when services are unhealthy
- **Timeout**: Enforce operation deadlines to prevent hung operations
- **Retry**: Automatically retry transient failures with exponential backoff

## Features

- ✅ **Production-ready**: Zero allocations in hot path, thread-safe, comprehensive tests
- ✅ **Observable**: State monitoring, statistics, callbacks
- ✅ **Composable**: Combine patterns (circuit breaker + timeout + retry)
- ✅ **Mathematical**: Based on Asymmetrica's three-regime dynamics
- ✅ **Fast**: 87ns/op for closed circuit, 48ns/op for open circuit

## Quick Start

### Circuit Breaker

```go
import "github.com/asymmetrica/urbanlens/pkg/resilience"

// Create circuit breaker
cb, err := resilience.NewCircuitBreaker("my-api", resilience.Config{
    Name:                  "my-api",
    FailureThreshold:      5,  // Open after 5 failures
    SuccessThreshold:      2,  // Close after 2 successes
    Timeout:               30 * time.Second,
    MaxConcurrentRequests: 1,
})

// Protect operations
err = cb.Execute(func() error {
    return callExternalAPI()
})

if errors.Is(err, resilience.ErrCircuitOpen) {
    // Circuit is open - fail fast
    return fallbackResponse()
}
```

### Timeout

```go
// Simple timeout
err := resilience.WithTimeout(5*time.Second, func(ctx context.Context) error {
    return slowOperation(ctx)
})

// Timeout with result
result, err := resilience.WithTimeoutResult(5*time.Second,
    func(ctx context.Context) (string, error) {
        return fetchData(ctx)
    })

// Predefined timeouts
resilience.WithAPITimeout(func(ctx context.Context) error {
    return callAPI(ctx)  // 10 second timeout
})

resilience.WithCognitionTimeout(func(ctx context.Context) (string, error) {
    return runLLM(ctx)  // 5 minute timeout
})
```

### Retry

```go
err := resilience.RetryWithTimeout(
    3,                    // Max retries
    10*time.Second,       // Timeout per attempt
    100*time.Millisecond, // Initial backoff
    func(ctx context.Context) error {
        return unreliableOperation(ctx)
    },
)
```

### Combined Pattern

```go
// Circuit breaker + timeout + retry
cb, _ := resilience.NewCircuitBreaker("api", resilience.DefaultConfig("api"))

err := cb.ExecuteWithContext(ctx, func(ctx context.Context) error {
    return resilience.RetryWithTimeout(3, 5*time.Second, 100*time.Millisecond,
        func(ctx context.Context) error {
            return resilience.WithTimeout(2*time.Second, func(ctx context.Context) error {
                return callAPI(ctx)
            })
        },
    )
})
```

## Circuit Breaker State Machine

```
CLOSED (normal)
    |
    | failures >= threshold
    v
OPEN (blocking)
    |
    | timeout elapsed
    v
HALF_OPEN (testing)
    |
    +-- success >= threshold --> CLOSED
    |
    +-- any failure ----------> OPEN
```

## Configuration

### Circuit Breaker Config

```go
type Config struct {
    Name                  string        // Circuit breaker name
    FailureThreshold      uint32        // Failures to open (default: 5)
    SuccessThreshold      uint32        // Successes to close (default: 2)
    Timeout               time.Duration // Time before half-open (default: 30s)
    MaxConcurrentRequests uint32        // Concurrent requests in half-open (default: 1)
    OnStateChange         func(from, to State) // Optional callback
}
```

### Default Configuration

```go
cb, _ := resilience.NewCircuitBreaker("my-service",
    resilience.DefaultConfig("my-service"))
// Uses: 5 failures, 2 successes, 30s timeout, 1 concurrent
```

## Observability

### Statistics

```go
stats := cb.GetStats()

fmt.Printf("State: %s\n", stats.State)
fmt.Printf("Total requests: %d\n", stats.TotalRequests)
fmt.Printf("Success rate: %.2f%%\n", stats.SuccessRate() * 100)
fmt.Printf("Consecutive failures: %d\n", stats.ConsecutiveFailures)
```

### State Monitoring

```go
config := resilience.Config{
    Name: "monitored",
    OnStateChange: func(from, to resilience.State) {
        log.Printf("Circuit %s: %s -> %s", config.Name, from, to)
        metrics.RecordStateChange(config.Name, to)

        if to == resilience.StateOpen {
            alerts.SendAlert("Circuit opened!")
        }
    },
}
```

### Current State

```go
switch cb.GetState() {
case resilience.StateClosed:
    // Normal operation
case resilience.StateOpen:
    // Failing fast
case resilience.StateHalfOpen:
    // Testing recovery
}
```

## Real-World Example

```go
// API client with full resilience
type APIClient struct {
    paymentCB *resilience.CircuitBreaker
    emailCB   *resilience.CircuitBreaker
}

func NewAPIClient() *APIClient {
    paymentCB, _ := resilience.NewCircuitBreaker("payment", resilience.Config{
        Name:                  "payment-api",
        FailureThreshold:      10,
        SuccessThreshold:      3,
        Timeout:               60 * time.Second,
        MaxConcurrentRequests: 5,
        OnStateChange: func(from, to resilience.State) {
            log.Printf("[PAYMENT] %s -> %s", from, to)
        },
    })

    emailCB, _ := resilience.NewCircuitBreaker("email", resilience.Config{
        Name:                  "email-api",
        FailureThreshold:      5,
        SuccessThreshold:      2,
        Timeout:               30 * time.Second,
        MaxConcurrentRequests: 10,
    })

    return &APIClient{paymentCB: paymentCB, emailCB: emailCB}
}

func (c *APIClient) ProcessPayment(ctx context.Context, amount float64) error {
    // Circuit breaker + retry + timeout
    return c.paymentCB.ExecuteWithContext(ctx, func(ctx context.Context) error {
        return resilience.RetryWithTimeout(3, 10*time.Second, 500*time.Millisecond,
            func(ctx context.Context) error {
                return c.callPaymentAPI(ctx, amount)
            },
        )
    })
}

func (c *APIClient) SendEmail(to, subject, body string) error {
    // Fire and forget with circuit breaker
    go func() {
        c.emailCB.Execute(func() error {
            return c.callEmailAPI(to, subject, body)
        })
    }()
    return nil
}
```

## Performance

Benchmarks on modern hardware:

```
BenchmarkCircuitBreakerClosed         87.26 ns/op   0 B/op   0 allocs/op
BenchmarkCircuitBreakerOpen           48.69 ns/op   0 B/op   0 allocs/op
BenchmarkCircuitBreakerConcurrent    178.3  ns/op   0 B/op   0 allocs/op
```

**Zero allocations** in steady state (CLOSED/OPEN) for maximum performance.

## Thread Safety

All types are **fully thread-safe** and designed for concurrent use:

```go
// Safe to call from multiple goroutines
var wg sync.WaitGroup
for i := 0; i < 1000; i++ {
    wg.Add(1)
    go func() {
        defer wg.Done()
        cb.Execute(func() error {
            return someOperation()
        })
    }()
}
wg.Wait()
```

## Testing

### Unit Tests

```bash
go test ./pkg/resilience/
```

### Benchmarks

```bash
go test -bench=. -benchmem ./pkg/resilience/
```

### Test Coverage

25+ comprehensive tests covering:
- ✅ State transitions (CLOSED → OPEN → HALF_OPEN → CLOSED)
- ✅ Threshold enforcement
- ✅ Timeout recovery
- ✅ Thread safety (10,000 concurrent operations)
- ✅ State callbacks
- ✅ Context support
- ✅ Configuration validation
- ✅ Statistics accuracy
- ✅ Reset functionality

## Mathematical Foundation

Based on Asymmetrica's **three-regime dynamics**:

- **Regime 1 (30%)**: Exploration - Testing recovery (HALF_OPEN state)
- **Regime 2 (20%)**: Optimization - Threshold evaluation (decision points)
- **Regime 3 (50%)**: Stabilization - Steady state (CLOSED/OPEN states)

State transitions follow **Markov chain dynamics** on S³ quaternion state space, ensuring mathematical stability and predictable behavior.

## Error Handling

### Circuit Breaker Errors

```go
err := cb.Execute(operation)

switch {
case errors.Is(err, resilience.ErrCircuitOpen):
    // Circuit is open - use fallback
    return fallbackValue

case errors.Is(err, resilience.ErrTooManyRequests):
    // Half-open concurrent limit exceeded
    return tryAgainLater

case errors.Is(err, resilience.ErrInvalidConfig):
    // Configuration error (at creation time)
    log.Fatal(err)

default:
    // Operation error
    return err
}
```

### Timeout Errors

```go
err := resilience.WithTimeout(5*time.Second, operation)

if errors.Is(err, context.DeadlineExceeded) {
    // Operation timed out
    return handleTimeout()
}
```

## Advanced Usage

### Custom State Logic

```go
// Use state for routing decisions
if cb.GetState() == resilience.StateOpen {
    // Route to backup service
    return callBackupService()
}

// Normal execution
return cb.Execute(func() error {
    return callPrimaryService()
})
```

### Manual Reset

```go
// Reset circuit breaker (use with caution!)
cb.Reset()

// Useful for:
// - Admin endpoints
// - Testing
// - Coordinated recovery
```

### Statistics Export

```go
// Export for monitoring
func exportMetrics(cb *resilience.CircuitBreaker) {
    stats := cb.GetStats()

    prometheus.CircuitBreakerState.Set(float64(stats.State))
    prometheus.CircuitBreakerRequests.Set(float64(stats.TotalRequests))
    prometheus.CircuitBreakerSuccessRate.Set(stats.SuccessRate())
    prometheus.CircuitBreakerConsecutiveFailures.Set(float64(stats.ConsecutiveFailures))
}
```

## Migration from Other Libraries

### From Netflix Hystrix (Java)

```go
// Hystrix
HystrixCommand<String> command = new HystrixCommand<>(config) {
    protected String run() { return "result"; }
};
String result = command.execute();

// Asymmetrica resilience
cb, _ := resilience.NewCircuitBreaker("my-command", config)
result, err := resilience.WithTimeoutResult(5*time.Second,
    func(ctx context.Context) (string, error) {
        return "result", nil
    })
```

### From resilience4j (Java)

```go
// resilience4j
CircuitBreaker cb = CircuitBreaker.ofDefaults("backend");
Supplier<String> supplier = CircuitBreaker
    .decorateSupplier(cb, () -> backendService.doSomething());

// Asymmetrica resilience
cb, _ := resilience.NewCircuitBreaker("backend", resilience.DefaultConfig("backend"))
result, err := resilience.WithTimeoutResult(5*time.Second,
    func(ctx context.Context) (string, error) {
        return backendService.DoSomething(ctx)
    })
```

## References

- [Release It! by Michael Nygard](https://pragprog.com/titles/mnee2/release-it-second-edition/)
- [Netflix Hystrix](https://github.com/Netflix/Hystrix)
- [resilience4j](https://github.com/resilience4j/resilience4j)
- [Asymmetrica Mathematical Standard](../../asymm_mathematical_organism/ASYMMETRICA_MATHEMATICAL_STANDARD.md)

## License

Part of the Asymmetrica Urban Lens project.

---

**Om Lokah Samastah Sukhino Bhavantu**
*May all beings benefit from resilient systems.*
