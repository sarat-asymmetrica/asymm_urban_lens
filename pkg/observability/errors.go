// Package observability provides standardized error handling and metrics
// for UrbanLens platform with Hamilton-grade reliability standards
package observability

import (
	"encoding/json"
	"fmt"
	"runtime"
	"time"

	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promauto"
)

// ═══════════════════════════════════════════════════════════════════════════
// SEVERITY LEVELS (Hamilton: "Every error must be documented")
// ═══════════════════════════════════════════════════════════════════════════

// Severity represents the criticality level of an error
type Severity int

const (
	// SeverityDebug - Development/debugging information (not an error)
	SeverityDebug Severity = iota

	// SeverityInfo - Informational events (successful operations)
	SeverityInfo

	// SeverityWarning - Warning conditions (degraded operation, fallback activated)
	// Examples: GPU unavailable (falling back to CPU), single sonar failure
	SeverityWarning

	// SeverityError - Error conditions (operation failed but system continues)
	// Examples: API timeout, multiple sonar failures, circuit breaker triggered
	SeverityError

	// SeverityCritical - Critical conditions (system instability imminent)
	// Examples: Memory pressure, database connection lost, cascade failures
	SeverityCritical

	// SeverityFatal - Fatal conditions (system cannot continue)
	// Examples: Core service initialization failed, unrecoverable panic
	SeverityFatal
)

func (s Severity) String() string {
	switch s {
	case SeverityDebug:
		return "DEBUG"
	case SeverityInfo:
		return "INFO"
	case SeverityWarning:
		return "WARNING"
	case SeverityError:
		return "ERROR"
	case SeverityCritical:
		return "CRITICAL"
	case SeverityFatal:
		return "FATAL"
	default:
		return "UNKNOWN"
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR CODES (Namespace: Category-Subcategory-Specific)
// ═══════════════════════════════════════════════════════════════════════════

const (
	// GPU Errors (GPU-*)
	ErrorGPUInitFailed        = "GPU-INIT-001"
	ErrorGPUMemoryExhausted   = "GPU-MEM-002"
	ErrorGPUKernelFailed      = "GPU-KERNEL-003"
	ErrorGPUDriverMismatch    = "GPU-DRIVER-004"
	ErrorGPUNotAvailable      = "GPU-AVAIL-005"

	// Sonar Errors (SONAR-*)
	ErrorSonarPingFailed      = "SONAR-PING-001"
	ErrorSonarEchoFailed      = "SONAR-ECHO-002"
	ErrorSonarMapFailed       = "SONAR-MAP-003"
	ErrorSonarCritiqueFailed  = "SONAR-CRITIQUE-004"
	ErrorSonarThresholdExceeded = "SONAR-THRESHOLD-005"
	ErrorSonarCascadeFail     = "SONAR-CASCADE-006"

	// API Errors (API-*)
	ErrorAPITimeout           = "API-TIMEOUT-001"
	ErrorAPIRateLimited       = "API-RATE-002"
	ErrorAPIAuthFailed        = "API-AUTH-003"
	ErrorAPIInvalidRequest    = "API-REQUEST-004"
	ErrorAPIServerError       = "API-SERVER-005"
	ErrorAPICircuitOpen       = "API-CIRCUIT-006"

	// Memory Errors (MEM-*)
	ErrorMemPressureHigh      = "MEM-PRESSURE-001"
	ErrorMemPressureCritical  = "MEM-PRESSURE-002"
	ErrorMemAllocationFailed  = "MEM-ALLOC-003"
	ErrorMemLeakDetected      = "MEM-LEAK-004"

	// Circuit Breaker Errors (CB-*)
	ErrorCBOpen               = "CB-OPEN-001"
	ErrorCBHalfOpenFailed     = "CB-HALFOPEN-002"
	ErrorCBThresholdExceeded  = "CB-THRESHOLD-003"

	// OCR Errors (OCR-*)
	ErrorOCRProcessingFailed  = "OCR-PROCESS-001"
	ErrorOCRQualityLow        = "OCR-QUALITY-002"
	ErrorOCRLanguageUnsupported = "OCR-LANG-003"
	ErrorOCRTimeoutExceeded   = "OCR-TIMEOUT-004"

	// Data Pipeline Errors (PIPELINE-*)
	ErrorPipelineStageFailed  = "PIPELINE-STAGE-001"
	ErrorPipelineValidationFailed = "PIPELINE-VALIDATE-002"
	ErrorPipelineTransformFailed = "PIPELINE-TRANSFORM-003"

	// Configuration Errors (CONFIG-*)
	ErrorConfigMissing        = "CONFIG-MISSING-001"
	ErrorConfigInvalid        = "CONFIG-INVALID-002"
	ErrorConfigParseFailed    = "CONFIG-PARSE-003"

	// Dependency Errors (DEP-*)
	ErrorDepUnavailable       = "DEP-UNAVAIL-001"
	ErrorDepVersionMismatch   = "DEP-VERSION-002"
	ErrorDepInitFailed        = "DEP-INIT-003"
)

// ═══════════════════════════════════════════════════════════════════════════
// URBANLENS ERROR (Standardized Error Type)
// ═══════════════════════════════════════════════════════════════════════════

// UrbanLensError is the standard error type for all UrbanLens operations
type UrbanLensError struct {
	Code      string                 `json:"code"`       // Error code (e.g., "GPU-INIT-001")
	Message   string                 `json:"message"`    // Human-readable message
	Severity  Severity               `json:"severity"`   // Severity level
	Cause     error                  `json:"-"`          // Underlying error (not serialized)
	Context   map[string]interface{} `json:"context"`    // Additional context
	Timestamp time.Time              `json:"timestamp"`  // When error occurred
	Stack     []StackFrame           `json:"stack"`      // Stack trace
	Retryable bool                   `json:"retryable"`  // Can this be retried?
}

// StackFrame represents a single stack frame
type StackFrame struct {
	Function string `json:"function"`
	File     string `json:"file"`
	Line     int    `json:"line"`
}

// Error implements the error interface
func (e *UrbanLensError) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("[%s] %s: %v", e.Code, e.Message, e.Cause)
	}
	return fmt.Sprintf("[%s] %s", e.Code, e.Message)
}

// Unwrap returns the underlying cause (for errors.Is/As)
func (e *UrbanLensError) Unwrap() error {
	return e.Cause
}

// WithContext adds context to the error (fluent interface)
func (e *UrbanLensError) WithContext(key string, value interface{}) *UrbanLensError {
	if e.Context == nil {
		e.Context = make(map[string]interface{})
	}
	e.Context[key] = value
	return e
}

// WithCause sets the underlying cause
func (e *UrbanLensError) WithCause(cause error) *UrbanLensError {
	e.Cause = cause
	return e
}

// AsRetryable marks error as retryable
func (e *UrbanLensError) AsRetryable() *UrbanLensError {
	e.Retryable = true
	return e
}

// JSON serializes error to JSON
func (e *UrbanLensError) JSON() ([]byte, error) {
	type alias struct {
		Code      string                 `json:"code"`
		Message   string                 `json:"message"`
		Severity  string                 `json:"severity"`
		Context   map[string]interface{} `json:"context"`
		Timestamp time.Time              `json:"timestamp"`
		Stack     []StackFrame           `json:"stack"`
		Retryable bool                   `json:"retryable"`
		Cause     string                 `json:"cause,omitempty"`
	}

	a := alias{
		Code:      e.Code,
		Message:   e.Message,
		Severity:  e.Severity.String(),
		Context:   e.Context,
		Timestamp: e.Timestamp,
		Stack:     e.Stack,
		Retryable: e.Retryable,
	}

	if e.Cause != nil {
		a.Cause = e.Cause.Error()
	}

	return json.Marshal(a)
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR CONSTRUCTORS
// ═══════════════════════════════════════════════════════════════════════════

// NewError creates a new UrbanLensError with stack trace
func NewError(code, message string, severity Severity) *UrbanLensError {
	return &UrbanLensError{
		Code:      code,
		Message:   message,
		Severity:  severity,
		Context:   make(map[string]interface{}),
		Timestamp: time.Now(),
		Stack:     captureStack(2), // Skip NewError and caller
		Retryable: false,
	}
}

// WrapError wraps an existing error with UrbanLens metadata
func WrapError(cause error, code, message string, severity Severity) *UrbanLensError {
	return &UrbanLensError{
		Code:      code,
		Message:   message,
		Severity:  severity,
		Cause:     cause,
		Context:   make(map[string]interface{}),
		Timestamp: time.Now(),
		Stack:     captureStack(2),
		Retryable: false,
	}
}

// captureStack captures the current stack trace
func captureStack(skip int) []StackFrame {
	const maxFrames = 10
	frames := make([]StackFrame, 0, maxFrames)

	// Capture up to maxFrames stack frames
	pc := make([]uintptr, maxFrames)
	n := runtime.Callers(skip+1, pc)
	if n == 0 {
		return frames
	}

	pc = pc[:n]
	callersFrames := runtime.CallersFrames(pc)

	for {
		frame, more := callersFrames.Next()
		frames = append(frames, StackFrame{
			Function: frame.Function,
			File:     frame.File,
			Line:     frame.Line,
		})

		if !more || len(frames) >= maxFrames {
			break
		}
	}

	return frames
}

// ═══════════════════════════════════════════════════════════════════════════
// PROMETHEUS METRICS
// ═══════════════════════════════════════════════════════════════════════════

var (
	// ErrorCounter tracks total errors by code and severity
	ErrorCounter = promauto.NewCounterVec(
		prometheus.CounterOpts{
			Namespace: "urbanlens",
			Subsystem: "errors",
			Name:      "total",
			Help:      "Total number of errors by code and severity",
		},
		[]string{"code", "severity"},
	)

	// ErrorRate tracks error rate over time windows
	ErrorRate = promauto.NewHistogramVec(
		prometheus.HistogramOpts{
			Namespace: "urbanlens",
			Subsystem: "errors",
			Name:      "rate_seconds",
			Help:      "Error rate distribution over time windows",
			Buckets:   prometheus.ExponentialBuckets(0.1, 2, 10), // 0.1s to 51.2s
		},
		[]string{"code"},
	)

	// RecoveryCounter tracks successful error recoveries
	RecoveryCounter = promauto.NewCounterVec(
		prometheus.CounterOpts{
			Namespace: "urbanlens",
			Subsystem: "errors",
			Name:      "recoveries_total",
			Help:      "Total number of successful error recoveries",
		},
		[]string{"code", "recovery_type"},
	)

	// RetryCounter tracks retry attempts
	RetryCounter = promauto.NewCounterVec(
		prometheus.CounterOpts{
			Namespace: "urbanlens",
			Subsystem: "errors",
			Name:      "retries_total",
			Help:      "Total number of retry attempts",
		},
		[]string{"code", "attempt"},
	)
)

// ═══════════════════════════════════════════════════════════════════════════
// ERROR RECORDING (Metrics Integration)
// ═══════════════════════════════════════════════════════════════════════════

// RecordError records an error to metrics
func RecordError(err *UrbanLensError) {
	ErrorCounter.WithLabelValues(err.Code, err.Severity.String()).Inc()
	ErrorRate.WithLabelValues(err.Code).Observe(time.Since(err.Timestamp).Seconds())
}

// RecordRecovery records a successful error recovery
func RecordRecovery(code, recoveryType string) {
	RecoveryCounter.WithLabelValues(code, recoveryType).Inc()
}

// RecordRetry records a retry attempt
func RecordRetry(code string, attempt int) {
	RetryCounter.WithLabelValues(code, fmt.Sprintf("%d", attempt)).Inc()
}

// ═══════════════════════════════════════════════════════════════════════════
// COMMON ERROR FACTORIES (Convenience Functions)
// ═══════════════════════════════════════════════════════════════════════════

// GPU Errors
func NewGPUInitError(cause error) *UrbanLensError {
	return WrapError(cause, ErrorGPUInitFailed, "GPU initialization failed", SeverityWarning).
		WithContext("fallback", "CPU mode available")
}

func NewGPUMemoryError(allocated, required int64) *UrbanLensError {
	return NewError(ErrorGPUMemoryExhausted, "GPU memory exhausted", SeverityCritical).
		WithContext("allocated_mb", allocated/(1024*1024)).
		WithContext("required_mb", required/(1024*1024))
}

func NewGPUNotAvailableError() *UrbanLensError {
	return NewError(ErrorGPUNotAvailable, "GPU not available on this system", SeverityWarning).
		WithContext("fallback", "CPU mode")
}

// Sonar Errors
func NewSonarPingError(sonarName string, cause error) *UrbanLensError {
	return WrapError(cause, ErrorSonarPingFailed, "Sonar ping failed", SeverityWarning).
		WithContext("sonar", sonarName).
		AsRetryable()
}

func NewSonarCascadeError(failedCount, totalCount int) *UrbanLensError {
	severity := SeverityWarning
	if failedCount > totalCount/2 {
		severity = SeverityError
	}
	return NewError(ErrorSonarCascadeFail, "Multiple sonars failed", severity).
		WithContext("failed_count", failedCount).
		WithContext("total_count", totalCount).
		WithContext("health_percentage", float64(totalCount-failedCount)/float64(totalCount)*100)
}

// API Errors
func NewAPITimeoutError(url string, timeout time.Duration) *UrbanLensError {
	return NewError(ErrorAPITimeout, "API request timed out", SeverityError).
		WithContext("url", url).
		WithContext("timeout_seconds", timeout.Seconds()).
		AsRetryable()
}

func NewAPICircuitOpenError(serviceName string) *UrbanLensError {
	return NewError(ErrorAPICircuitOpen, "Circuit breaker is open", SeverityWarning).
		WithContext("service", serviceName).
		WithContext("action", "wait for recovery")
}

// Memory Errors
func NewMemoryPressureError(usedPercent float64) *UrbanLensError {
	severity := SeverityWarning
	if usedPercent > 90.0 {
		severity = SeverityCritical
	}
	return NewError(ErrorMemPressureHigh, "Memory pressure detected", severity).
		WithContext("used_percent", usedPercent).
		WithContext("action", "shedding load")
}

// Circuit Breaker Errors
func NewCircuitBreakerError(serviceName string, failureRate float64) *UrbanLensError {
	return NewError(ErrorCBOpen, "Circuit breaker opened", SeverityWarning).
		WithContext("service", serviceName).
		WithContext("failure_rate", failureRate).
		WithContext("recovery_action", "exponential backoff")
}

// OCR Errors
func NewOCRProcessingError(filename string, cause error) *UrbanLensError {
	return WrapError(cause, ErrorOCRProcessingFailed, "OCR processing failed", SeverityError).
		WithContext("file", filename).
		AsRetryable()
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR CATEGORIZATION
// ═══════════════════════════════════════════════════════════════════════════

// ErrorCategory represents the category of an error
type ErrorCategory string

const (
	CategoryGPU       ErrorCategory = "GPU"
	CategorySonar     ErrorCategory = "Sonar"
	CategoryAPI       ErrorCategory = "API"
	CategoryMemory    ErrorCategory = "Memory"
	CategoryCircuit   ErrorCategory = "CircuitBreaker"
	CategoryOCR       ErrorCategory = "OCR"
	CategoryPipeline  ErrorCategory = "Pipeline"
	CategoryConfig    ErrorCategory = "Configuration"
	CategoryDependency ErrorCategory = "Dependency"
)

// GetCategory extracts category from error code (e.g., "GPU-INIT-001" -> "GPU")
func GetCategory(code string) ErrorCategory {
	// Parse code prefix and map to full category name
	for i, ch := range code {
		if ch == '-' {
			prefix := code[:i]
			// Map prefix to full category name
			switch prefix {
			case "GPU":
				return CategoryGPU
			case "SONAR":
				return CategorySonar
			case "API":
				return CategoryAPI
			case "MEM":
				return CategoryMemory
			case "CB":
				return CategoryCircuit
			case "OCR":
				return CategoryOCR
			case "PIPELINE":
				return CategoryPipeline
			case "CONFIG":
				return CategoryConfig
			case "DEP":
				return CategoryDependency
			default:
				return ErrorCategory(prefix)
			}
		}
	}
	return ErrorCategory("UNKNOWN")
}

// IsRetryable determines if an error should be retried
func IsRetryable(err error) bool {
	if ulErr, ok := err.(*UrbanLensError); ok {
		return ulErr.Retryable
	}
	return false
}

// GetSeverity extracts severity from error
func GetSeverity(err error) Severity {
	if ulErr, ok := err.(*UrbanLensError); ok {
		return ulErr.Severity
	}
	return SeverityError // Default to ERROR for unknown errors
}
