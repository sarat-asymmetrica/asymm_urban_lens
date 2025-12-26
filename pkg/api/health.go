// Package api - Health Check and System Status
package api

import (
	"os/exec"
	"runtime"
	"strings"
	"time"
)

// HealthStatus represents the overall system health
type HealthStatus struct {
	Status     string                      `json:"status"` // "healthy", "degraded", "unhealthy"
	Version    string                      `json:"version"`
	Uptime     string                      `json:"uptime"`
	Timestamp  string                      `json:"timestamp"`
	Components map[string]*ComponentStatus `json:"components"`
	System     *SystemInfo                 `json:"system"`
}

// ComponentStatus represents health of a single component
type ComponentStatus struct {
	Status  string `json:"status"` // "ok", "degraded", "error"
	Message string `json:"message,omitempty"`
	Version string `json:"version,omitempty"`
}

// SystemInfo contains system resource information
type SystemInfo struct {
	GoVersion    string  `json:"go_version"`
	NumCPU       int     `json:"num_cpu"`
	NumGoroutine int     `json:"num_goroutine"`
	MemAllocMB   float64 `json:"mem_alloc_mb"`
	OS           string  `json:"os"`
	Arch         string  `json:"arch"`
}

// HealthChecker manages health checks for the system
type HealthChecker struct {
	startTime time.Time
	version   string
}

// NewHealthChecker creates a new health checker
func NewHealthChecker(version string) *HealthChecker {
	return &HealthChecker{
		startTime: time.Now(),
		version:   version,
	}
}

// Check performs a full health check
func (h *HealthChecker) Check() *HealthStatus {
	components := make(map[string]*ComponentStatus)

	// Check external tools
	components["pandoc"] = h.checkTool("pandoc", "--version")
	components["ffmpeg"] = h.checkTool("ffmpeg", "-version")
	components["tesseract"] = h.checkTool("tesseract", "--version")

	// Determine overall status
	overallStatus := "healthy"
	for _, comp := range components {
		if comp.Status == "error" {
			overallStatus = "degraded"
			break
		}
	}

	// Get system info
	var memStats runtime.MemStats
	runtime.ReadMemStats(&memStats)

	return &HealthStatus{
		Status:     overallStatus,
		Version:    h.version,
		Uptime:     time.Since(h.startTime).Round(time.Second).String(),
		Timestamp:  time.Now().UTC().Format(time.RFC3339),
		Components: components,
		System: &SystemInfo{
			GoVersion:    runtime.Version(),
			NumCPU:       runtime.NumCPU(),
			NumGoroutine: runtime.NumGoroutine(),
			MemAllocMB:   float64(memStats.Alloc) / 1024 / 1024,
			OS:           runtime.GOOS,
			Arch:         runtime.GOARCH,
		},
	}
}

// checkTool checks if an external tool is available
func (h *HealthChecker) checkTool(name string, versionArg string) *ComponentStatus {
	cmd := exec.Command(name, versionArg)
	output, err := cmd.Output()

	if err != nil {
		return &ComponentStatus{
			Status:  "error",
			Message: "Not installed or not in PATH",
		}
	}

	// Extract first line as version
	version := strings.Split(string(output), "\n")[0]
	if len(version) > 60 {
		version = version[:60] + "..."
	}

	return &ComponentStatus{
		Status:  "ok",
		Version: strings.TrimSpace(version),
	}
}

// QuickCheck performs a minimal health check (for load balancers)
func (h *HealthChecker) QuickCheck() map[string]interface{} {
	return map[string]interface{}{
		"status":    "ok",
		"version":   h.version,
		"timestamp": time.Now().UTC().Format(time.RFC3339),
	}
}
