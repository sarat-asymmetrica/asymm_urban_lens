// Package api provides standardized API response structures
// Ensures consistent error handling and response formatting across all endpoints
package api

import (
	"encoding/json"
	"net/http"
	"time"
)

// Response represents a standardized API response
type Response struct {
	Success   bool        `json:"success"`
	Data      interface{} `json:"data,omitempty"`
	Error     *ErrorInfo  `json:"error,omitempty"`
	Meta      *MetaInfo   `json:"meta,omitempty"`
	Timestamp string      `json:"timestamp"`
}

// ErrorInfo contains detailed error information
type ErrorInfo struct {
	Code    string `json:"code"`
	Message string `json:"message"`
	Details string `json:"details,omitempty"`
	Help    string `json:"help,omitempty"`
}

// MetaInfo contains response metadata
type MetaInfo struct {
	RequestID   string  `json:"request_id,omitempty"`
	ProcessTime float64 `json:"process_time_ms,omitempty"`
	Version     string  `json:"version,omitempty"`
}

// Common error codes
const (
	ErrCodeBadRequest   = "BAD_REQUEST"
	ErrCodeNotFound     = "NOT_FOUND"
	ErrCodeInternal     = "INTERNAL_ERROR"
	ErrCodeUnavailable  = "SERVICE_UNAVAILABLE"
	ErrCodeValidation   = "VALIDATION_ERROR"
	ErrCodeUnauthorized = "UNAUTHORIZED"
	ErrCodeRateLimit    = "RATE_LIMITED"
	ErrCodeToolMissing  = "TOOL_NOT_AVAILABLE"
)

// JSON sends a successful JSON response
func JSON(w http.ResponseWriter, data interface{}, meta *MetaInfo) {
	resp := Response{
		Success:   true,
		Data:      data,
		Meta:      meta,
		Timestamp: time.Now().UTC().Format(time.RFC3339),
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(resp)
}

// Error sends an error JSON response
func Error(w http.ResponseWriter, statusCode int, code, message string, details string) {
	resp := Response{
		Success: false,
		Error: &ErrorInfo{
			Code:    code,
			Message: message,
			Details: details,
		},
		Timestamp: time.Now().UTC().Format(time.RFC3339),
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(statusCode)
	json.NewEncoder(w).Encode(resp)
}

// ErrorWithHelp sends an error with helpful guidance
func ErrorWithHelp(w http.ResponseWriter, statusCode int, code, message, details, help string) {
	resp := Response{
		Success: false,
		Error: &ErrorInfo{
			Code:    code,
			Message: message,
			Details: details,
			Help:    help,
		},
		Timestamp: time.Now().UTC().Format(time.RFC3339),
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(statusCode)
	json.NewEncoder(w).Encode(resp)
}

// BadRequest sends a 400 error
func BadRequest(w http.ResponseWriter, message string) {
	Error(w, http.StatusBadRequest, ErrCodeBadRequest, message, "")
}

// NotFound sends a 404 error
func NotFound(w http.ResponseWriter, message string) {
	Error(w, http.StatusNotFound, ErrCodeNotFound, message, "")
}

// InternalError sends a 500 error
func InternalError(w http.ResponseWriter, message string, err error) {
	details := ""
	if err != nil {
		details = err.Error()
	}
	Error(w, http.StatusInternalServerError, ErrCodeInternal, message, details)
}

// ToolUnavailable sends an error when a required tool is missing
func ToolUnavailable(w http.ResponseWriter, toolName string, installHelp string) {
	ErrorWithHelp(w, http.StatusServiceUnavailable, ErrCodeToolMissing,
		toolName+" is not available",
		"This feature requires "+toolName+" to be installed",
		installHelp,
	)
}

// ValidationError sends a 422 error for validation failures
func ValidationError(w http.ResponseWriter, message string, details string) {
	Error(w, http.StatusUnprocessableEntity, ErrCodeValidation, message, details)
}

// MethodNotAllowed sends a 405 error
func MethodNotAllowed(w http.ResponseWriter, allowed string) {
	w.Header().Set("Allow", allowed)
	Error(w, http.StatusMethodNotAllowed, "METHOD_NOT_ALLOWED",
		"Method not allowed", "Allowed methods: "+allowed)
}

// WithCORS adds CORS headers for development
func WithCORS(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Access-Control-Allow-Origin", "*")
		w.Header().Set("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
		w.Header().Set("Access-Control-Allow-Headers", "Content-Type, Authorization")

		if r.Method == "OPTIONS" {
			w.WriteHeader(http.StatusOK)
			return
		}

		next(w, r)
	}
}

// WithRequestID adds a request ID to the response
func WithRequestID(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		requestID := r.Header.Get("X-Request-ID")
		if requestID == "" {
			requestID = generateRequestID()
		}
		w.Header().Set("X-Request-ID", requestID)
		next(w, r)
	}
}

// generateRequestID creates a simple request ID
func generateRequestID() string {
	return time.Now().Format("20060102150405") + "-" + randomString(6)
}

// randomString generates a random alphanumeric string
func randomString(n int) string {
	const letters = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	for i := range b {
		b[i] = letters[time.Now().UnixNano()%int64(len(letters))]
		time.Sleep(time.Nanosecond) // Ensure different values
	}
	return string(b)
}
