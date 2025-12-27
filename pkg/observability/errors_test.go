package observability

import (
	"errors"
	"testing"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// ERROR CREATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestNewError(t *testing.T) {
	err := NewError(ErrorGPUInitFailed, "GPU init failed", SeverityWarning)

	if err.Code != ErrorGPUInitFailed {
		t.Errorf("Expected code %s, got %s", ErrorGPUInitFailed, err.Code)
	}

	if err.Message != "GPU init failed" {
		t.Errorf("Expected message 'GPU init failed', got '%s'", err.Message)
	}

	if err.Severity != SeverityWarning {
		t.Errorf("Expected severity WARNING, got %s", err.Severity)
	}

	if err.Context == nil {
		t.Error("Expected context to be initialized")
	}

	if err.Timestamp.IsZero() {
		t.Error("Expected timestamp to be set")
	}

	if len(err.Stack) == 0 {
		t.Error("Expected stack trace to be captured")
	}
}

func TestWrapError(t *testing.T) {
	cause := errors.New("underlying error")
	err := WrapError(cause, ErrorAPITimeout, "API timeout", SeverityError)

	if err.Cause != cause {
		t.Error("Expected cause to be set")
	}

	if !errors.Is(err, cause) {
		t.Error("Expected errors.Is to work with wrapped error")
	}

	expectedMsg := "[API-TIMEOUT-001] API timeout: underlying error"
	if err.Error() != expectedMsg {
		t.Errorf("Expected error message '%s', got '%s'", expectedMsg, err.Error())
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// FLUENT INTERFACE TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestErrorWithContext(t *testing.T) {
	err := NewError(ErrorGPUMemoryExhausted, "Out of memory", SeverityCritical).
		WithContext("allocated_mb", 8192).
		WithContext("required_mb", 16384)

	if allocated, ok := err.Context["allocated_mb"].(int); !ok || allocated != 8192 {
		t.Error("Expected allocated_mb context to be 8192")
	}

	if required, ok := err.Context["required_mb"].(int); !ok || required != 16384 {
		t.Error("Expected required_mb context to be 16384")
	}
}

func TestErrorAsRetryable(t *testing.T) {
	err := NewError(ErrorAPITimeout, "Timeout", SeverityError).AsRetryable()

	if !err.Retryable {
		t.Error("Expected error to be marked as retryable")
	}

	if !IsRetryable(err) {
		t.Error("Expected IsRetryable to return true")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// SEVERITY TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestSeverityString(t *testing.T) {
	tests := []struct {
		severity Severity
		expected string
	}{
		{SeverityDebug, "DEBUG"},
		{SeverityInfo, "INFO"},
		{SeverityWarning, "WARNING"},
		{SeverityError, "ERROR"},
		{SeverityCritical, "CRITICAL"},
		{SeverityFatal, "FATAL"},
	}

	for _, tt := range tests {
		if tt.severity.String() != tt.expected {
			t.Errorf("Expected %s, got %s", tt.expected, tt.severity.String())
		}
	}
}

func TestGetSeverity(t *testing.T) {
	err := NewError(ErrorGPUInitFailed, "GPU error", SeverityWarning)
	severity := GetSeverity(err)

	if severity != SeverityWarning {
		t.Errorf("Expected WARNING severity, got %s", severity)
	}

	// Test with standard error
	stdErr := errors.New("standard error")
	severity = GetSeverity(stdErr)

	if severity != SeverityError {
		t.Errorf("Expected ERROR default severity, got %s", severity)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR FACTORY TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestNewGPUInitError(t *testing.T) {
	cause := errors.New("driver not found")
	err := NewGPUInitError(cause)

	if err.Code != ErrorGPUInitFailed {
		t.Errorf("Expected code %s, got %s", ErrorGPUInitFailed, err.Code)
	}

	if err.Severity != SeverityWarning {
		t.Errorf("Expected WARNING severity, got %s", err.Severity)
	}

	if fallback, ok := err.Context["fallback"].(string); !ok || fallback != "CPU mode available" {
		t.Error("Expected fallback context to be set")
	}

	if err.Cause != cause {
		t.Error("Expected cause to be set")
	}
}

func TestNewGPUMemoryError(t *testing.T) {
	err := NewGPUMemoryError(8*1024*1024*1024, 16*1024*1024*1024) // 8GB allocated, 16GB required

	if err.Code != ErrorGPUMemoryExhausted {
		t.Errorf("Expected code %s, got %s", ErrorGPUMemoryExhausted, err.Code)
	}

	if err.Severity != SeverityCritical {
		t.Errorf("Expected CRITICAL severity, got %s", err.Severity)
	}

	allocated, _ := err.Context["allocated_mb"].(int64)
	required, _ := err.Context["required_mb"].(int64)

	if allocated != 8192 {
		t.Errorf("Expected allocated 8192 MB, got %d", allocated)
	}

	if required != 16384 {
		t.Errorf("Expected required 16384 MB, got %d", required)
	}
}

func TestNewSonarPingError(t *testing.T) {
	cause := errors.New("network timeout")
	err := NewSonarPingError("CodeSonar", cause)

	if err.Code != ErrorSonarPingFailed {
		t.Errorf("Expected code %s, got %s", ErrorSonarPingFailed, err.Code)
	}

	if !err.Retryable {
		t.Error("Expected sonar ping error to be retryable")
	}

	if sonar, ok := err.Context["sonar"].(string); !ok || sonar != "CodeSonar" {
		t.Error("Expected sonar context to be 'CodeSonar'")
	}
}

func TestNewSonarCascadeError(t *testing.T) {
	// Test with minor failure (2 out of 5 failed = WARNING)
	err := NewSonarCascadeError(2, 5)
	if err.Severity != SeverityWarning {
		t.Errorf("Expected WARNING for minor cascade, got %s", err.Severity)
	}

	// Test with major failure (4 out of 5 failed = ERROR)
	err = NewSonarCascadeError(4, 5)
	if err.Severity != SeverityError {
		t.Errorf("Expected ERROR for major cascade, got %s", err.Severity)
	}

	health, _ := err.Context["health_percentage"].(float64)
	expectedHealth := 20.0 // 1 out of 5 working = 20%
	if health != expectedHealth {
		t.Errorf("Expected health %.1f%%, got %.1f%%", expectedHealth, health)
	}
}

func TestNewAPITimeoutError(t *testing.T) {
	err := NewAPITimeoutError("https://api.example.com/data", 30*time.Second)

	if err.Code != ErrorAPITimeout {
		t.Errorf("Expected code %s, got %s", ErrorAPITimeout, err.Code)
	}

	if !err.Retryable {
		t.Error("Expected API timeout to be retryable")
	}

	timeout, _ := err.Context["timeout_seconds"].(float64)
	if timeout != 30.0 {
		t.Errorf("Expected timeout 30.0s, got %.1f", timeout)
	}
}

func TestNewAPICircuitOpenError(t *testing.T) {
	err := NewAPICircuitOpenError("payment-service")

	if err.Code != ErrorAPICircuitOpen {
		t.Errorf("Expected code %s, got %s", ErrorAPICircuitOpen, err.Code)
	}

	if err.Severity != SeverityWarning {
		t.Errorf("Expected WARNING severity, got %s", err.Severity)
	}

	service, _ := err.Context["service"].(string)
	if service != "payment-service" {
		t.Errorf("Expected service 'payment-service', got '%s'", service)
	}

	action, _ := err.Context["action"].(string)
	if action != "wait for recovery" {
		t.Errorf("Expected action 'wait for recovery', got '%s'", action)
	}
}

func TestNewMemoryPressureError(t *testing.T) {
	// Test WARNING level (85% usage)
	err := NewMemoryPressureError(85.0)
	if err.Severity != SeverityWarning {
		t.Errorf("Expected WARNING for 85%% usage, got %s", err.Severity)
	}

	// Test CRITICAL level (95% usage)
	err = NewMemoryPressureError(95.0)
	if err.Severity != SeverityCritical {
		t.Errorf("Expected CRITICAL for 95%% usage, got %s", err.Severity)
	}

	usedPercent, _ := err.Context["used_percent"].(float64)
	if usedPercent != 95.0 {
		t.Errorf("Expected used_percent 95.0, got %.1f", usedPercent)
	}
}

func TestNewCircuitBreakerError(t *testing.T) {
	err := NewCircuitBreakerError("ai-inference", 0.75)

	if err.Code != ErrorCBOpen {
		t.Errorf("Expected code %s, got %s", ErrorCBOpen, err.Code)
	}

	failureRate, _ := err.Context["failure_rate"].(float64)
	if failureRate != 0.75 {
		t.Errorf("Expected failure_rate 0.75, got %.2f", failureRate)
	}
}

func TestNewOCRProcessingError(t *testing.T) {
	cause := errors.New("image corrupted")
	err := NewOCRProcessingError("document.pdf", cause)

	if err.Code != ErrorOCRProcessingFailed {
		t.Errorf("Expected code %s, got %s", ErrorOCRProcessingFailed, err.Code)
	}

	if !err.Retryable {
		t.Error("Expected OCR error to be retryable")
	}

	file, _ := err.Context["file"].(string)
	if file != "document.pdf" {
		t.Errorf("Expected file 'document.pdf', got '%s'", file)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR CATEGORIZATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestGetCategory(t *testing.T) {
	tests := []struct {
		code     string
		expected ErrorCategory
	}{
		{ErrorGPUInitFailed, CategoryGPU},
		{ErrorSonarPingFailed, CategorySonar},
		{ErrorAPITimeout, CategoryAPI},
		{ErrorMemPressureHigh, CategoryMemory},
		{ErrorCBOpen, CategoryCircuit},
		{ErrorOCRProcessingFailed, CategoryOCR},
	}

	for _, tt := range tests {
		category := GetCategory(tt.code)
		if category != tt.expected {
			t.Errorf("For code %s, expected category %s, got %s", tt.code, tt.expected, category)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// JSON SERIALIZATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestErrorJSON(t *testing.T) {
	err := NewError(ErrorGPUInitFailed, "GPU init failed", SeverityWarning).
		WithContext("device", "NVIDIA RTX 4090").
		WithContext("driver_version", "535.104.05")

	jsonBytes, jsonErr := err.JSON()
	if jsonErr != nil {
		t.Fatalf("Error serializing to JSON: %v", jsonErr)
	}

	if len(jsonBytes) == 0 {
		t.Error("Expected non-empty JSON output")
	}

	// Verify JSON contains expected fields
	jsonStr := string(jsonBytes)
	expectedFields := []string{
		`"code":"GPU-INIT-001"`,
		`"message":"GPU init failed"`,
		`"severity":"WARNING"`,
		`"device":"NVIDIA RTX 4090"`,
	}

	for _, field := range expectedFields {
		if !contains(jsonStr, field) {
			t.Errorf("Expected JSON to contain '%s'", field)
		}
	}
}

func TestErrorJSONWithCause(t *testing.T) {
	cause := errors.New("driver not loaded")
	err := WrapError(cause, ErrorGPUInitFailed, "GPU init failed", SeverityWarning)

	jsonBytes, jsonErr := err.JSON()
	if jsonErr != nil {
		t.Fatalf("Error serializing to JSON: %v", jsonErr)
	}

	jsonStr := string(jsonBytes)
	if !contains(jsonStr, `"cause":"driver not loaded"`) {
		t.Error("Expected JSON to contain cause field")
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// STACK TRACE TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestStackTraceCapture(t *testing.T) {
	err := NewError(ErrorAPITimeout, "Timeout", SeverityError)

	if len(err.Stack) == 0 {
		t.Error("Expected stack trace to be captured")
	}

	// First frame should be in this test file
	if len(err.Stack) > 0 {
		frame := err.Stack[0]
		if frame.Function == "" {
			t.Error("Expected function name in stack frame")
		}
		if frame.Line == 0 {
			t.Error("Expected line number in stack frame")
		}
		if !contains(frame.File, "errors_test.go") {
			t.Errorf("Expected stack frame to reference errors_test.go, got %s", frame.File)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// METRICS RECORDING TESTS
// ═══════════════════════════════════════════════════════════════════════════

func TestRecordError(t *testing.T) {
	err := NewError(ErrorGPUInitFailed, "GPU init failed", SeverityWarning)

	// This should not panic
	RecordError(err)
}

func TestRecordRecovery(t *testing.T) {
	// This should not panic
	RecordRecovery(ErrorGPUInitFailed, "fallback_cpu")
}

func TestRecordRetry(t *testing.T) {
	// This should not panic
	RecordRetry(ErrorAPITimeout, 1)
	RecordRetry(ErrorAPITimeout, 2)
	RecordRetry(ErrorAPITimeout, 3)
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && containsHelper(s, substr))
}

func containsHelper(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
