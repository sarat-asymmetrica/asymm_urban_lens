package observability

import (
	"context"
	"errors"
	"fmt"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// EXAMPLE INTEGRATION: How to use UrbanLens error handling in real code
// ═══════════════════════════════════════════════════════════════════════════

// ExampleGPUInitialization shows how to handle GPU initialization with fallback
func ExampleGPUInitialization() error {
	// Try to initialize GPU
	_, err := initializeGPU()
	if err != nil {
		// Create standardized error
		gpuErr := NewGPUInitError(err)

		// Record to metrics
		RecordError(gpuErr)

		// Log error (would be picked up by Loki/Grafana)
		fmt.Printf("WARNING: %s - falling back to CPU mode\n", gpuErr.Error())

		// Use CPU fallback
		RecordRecovery(ErrorGPUInitFailed, "fallback_cpu")
		useCPUMode()

		// Return nil - we recovered successfully
		return nil
	}

	fmt.Println("GPU initialized successfully")
	return nil
}

// ExampleSonarPing shows how to ping a sonar with retry logic
func ExampleSonarPing(ctx context.Context) error {
	maxRetries := 3
	baseDelay := 1 * time.Second

	for attempt := 0; attempt < maxRetries; attempt++ {
		// Attempt to ping sonar
		telemetry, err := pingSonar(ctx, "CodeSonar")

		if err == nil {
			fmt.Printf("Sonar ping successful: %v\n", telemetry)
			return nil
		}

		// Create error with context
		sonarErr := NewSonarPingError("CodeSonar", err).
			WithContext("attempt", attempt+1).
			WithContext("max_retries", maxRetries)

		// Record error
		RecordError(sonarErr)

		// Record retry attempt
		RecordRetry(ErrorSonarPingFailed, attempt+1)

		// Check if we should retry
		if !sonarErr.Retryable || attempt == maxRetries-1 {
			return sonarErr
		}

		// Exponential backoff
		delay := baseDelay * (1 << attempt)
		fmt.Printf("Sonar ping failed (attempt %d/%d), retrying in %v\n",
			attempt+1, maxRetries, delay)

		select {
		case <-time.After(delay):
			// Continue to next attempt
		case <-ctx.Done():
			return ctx.Err()
		}
	}

	return fmt.Errorf("max retries exceeded")
}

// ExampleAPICallWithCircuitBreaker shows API call with circuit breaker
func ExampleAPICallWithCircuitBreaker(ctx context.Context, url string) (interface{}, error) {
	// Check circuit breaker state first
	if circuitBreakerOpen("api-service") {
		err := NewAPICircuitOpenError("api-service")
		RecordError(err)

		// Use cached fallback
		cached := getCachedResponse(url)
		if cached != nil {
			fmt.Println("Circuit open, using cached response")
			RecordRecovery(ErrorAPICircuitOpen, "cached_response")
			return cached, nil
		}

		return nil, err
	}

	// Call API with timeout
	callCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()

	resp, err := callAPI(callCtx, url)

	if err != nil {
		// Check if timeout
		if errors.Is(err, context.DeadlineExceeded) {
			timeoutErr := NewAPITimeoutError(url, 30*time.Second)
			RecordError(timeoutErr)

			// Retry logic would go here
			fmt.Printf("API timeout, will retry: %s\n", timeoutErr.Error())

			return nil, timeoutErr
		}

		// Other API error
		apiErr := WrapError(err, ErrorAPIServerError, "API call failed", SeverityError).
			WithContext("url", url).
			WithContext("method", "GET")

		RecordError(apiErr)
		return nil, apiErr
	}

	return resp, nil
}

// ExampleMemoryPressureMonitoring shows how to monitor and handle memory pressure
func ExampleMemoryPressureMonitoring(ctx context.Context) {
	ticker := time.NewTicker(10 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			// Get current memory usage
			usedPercent := getMemoryUsagePercent()

			// Check for memory pressure
			if usedPercent > 90.0 {
				err := NewMemoryPressureError(usedPercent)
				RecordError(err)

				fmt.Printf("CRITICAL: Memory pressure %.1f%% - shedding load\n", usedPercent)

				// Aggressive load shedding
				setLoadSheddingThreshold(0.1) // Accept only 10% of requests

			} else if usedPercent > 80.0 {
				err := NewMemoryPressureError(usedPercent)
				RecordError(err)

				fmt.Printf("WARNING: Memory pressure %.1f%% - reducing load\n", usedPercent)

				// Moderate load shedding
				setLoadSheddingThreshold(0.5) // Accept 50% of requests

				// Trigger garbage collection
				forceGarbageCollection()

				// Evict cache
				evictCacheLRU(0.2) // Evict 20% of cache entries

				RecordRecovery(ErrorMemPressureHigh, "load_shedding")
			}

		case <-ctx.Done():
			return
		}
	}
}

// ExampleOCRPipelineWithFallback shows OCR processing with fallback engines
func ExampleOCRPipelineWithFallback(ctx context.Context, filename string) (string, error) {
	// Try Florence-2 (GPU-accelerated, high quality)
	text, err := processWithFlorence2(ctx, filename)
	if err == nil && len(text) > 0 {
		fmt.Println("OCR successful with Florence-2")
		return text, nil
	}

	if err != nil {
		ocrErr := NewOCRProcessingError(filename, err).
			WithContext("engine", "florence-2").
			WithContext("fallback", "tesseract")

		RecordError(ocrErr)
		fmt.Printf("Florence-2 failed, trying Tesseract: %s\n", err)
	}

	// Fallback to Tesseract (CPU-based, moderate quality)
	text, err = processWithTesseract(ctx, filename)
	if err == nil && len(text) > 0 {
		fmt.Println("OCR successful with Tesseract (fallback)")
		RecordRecovery(ErrorOCRProcessingFailed, "fallback_tesseract")
		return text, nil
	}

	if err != nil {
		ocrErr := NewOCRProcessingError(filename, err).
			WithContext("engine", "tesseract").
			WithContext("status", "manual_review_required")

		RecordError(ocrErr)
		return "", ocrErr
	}

	return text, nil
}

// ExampleSonarCascadeDetection shows how to detect and handle cascade failures
func ExampleSonarCascadeDetection(ctx context.Context) error {
	sonars := []string{"CodeSonar", "DesignSonar", "SemanticSonar", "JourneySonar", "StateSonar"}
	results := make(map[string]error)

	// Ping all sonars in parallel
	for _, sonarName := range sonars {
		_, err := pingSonar(ctx, sonarName)
		results[sonarName] = err
	}

	// Count failures
	failedCount := 0
	for _, err := range results {
		if err != nil {
			failedCount++
		}
	}

	// Check for cascade failure
	healthPercent := float64(len(sonars)-failedCount) / float64(len(sonars)) * 100

	if healthPercent < 50.0 {
		cascadeErr := NewSonarCascadeError(failedCount, len(sonars))
		RecordError(cascadeErr)

		fmt.Printf("ERROR: Sonar cascade failure - %.1f%% health\n", healthPercent)

		// List failed sonars
		for name, err := range results {
			if err != nil {
				fmt.Printf("  - %s: FAILED (%v)\n", name, err)
			}
		}

		return cascadeErr
	}

	if failedCount > 0 {
		fmt.Printf("WARNING: %d/%d sonars failed (%.1f%% health)\n",
			failedCount, len(sonars), healthPercent)
	} else {
		fmt.Println("All sonars healthy")
	}

	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// MOCK FUNCTIONS (Replace with real implementations)
// ═══════════════════════════════════════════════════════════════════════════

func initializeGPU() (interface{}, error) {
	// Mock: Simulate GPU init failure
	return nil, errors.New("driver not found")
}

func useCPUMode() {
	fmt.Println("  → Running in CPU mode")
}

func pingSonar(ctx context.Context, name string) (interface{}, error) {
	// Mock: Simulate sonar ping
	return map[string]interface{}{"sonar": name, "status": "ok"}, nil
}

func circuitBreakerOpen(service string) bool {
	// Mock: Check circuit breaker state
	return false
}

func callAPI(ctx context.Context, url string) (interface{}, error) {
	// Mock: Simulate API call
	return map[string]interface{}{"data": "response"}, nil
}

func getCachedResponse(url string) interface{} {
	// Mock: Get cached response
	return map[string]interface{}{"data": "cached", "url": url}
}

func getMemoryUsagePercent() float64 {
	// Mock: Return current memory usage
	return 75.0 // 75% usage
}

func setLoadSheddingThreshold(threshold float64) {
	fmt.Printf("  → Load shedding threshold set to %.1f%%\n", threshold*100)
}

func forceGarbageCollection() {
	fmt.Println("  → Triggering garbage collection")
}

func evictCacheLRU(percent float64) {
	fmt.Printf("  → Evicting %.1f%% of cache entries\n", percent*100)
}

func processWithFlorence2(ctx context.Context, filename string) (string, error) {
	// Mock: Simulate Florence-2 OCR
	return "", errors.New("GPU memory exhausted")
}

func processWithTesseract(ctx context.Context, filename string) (string, error) {
	// Mock: Simulate Tesseract OCR
	return "Extracted text from document", nil
}
