// Package tests - Integration tests for Urban Lens API
package tests

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/asymmetrica/urbanlens/pkg/api"
)

func TestHealthChecker(t *testing.T) {
	hc := api.NewHealthChecker("0.4.0")

	t.Run("QuickCheck", func(t *testing.T) {
		result := hc.QuickCheck()

		if result["status"] != "ok" {
			t.Errorf("Expected status 'ok', got %v", result["status"])
		}
		if result["version"] != "0.4.0" {
			t.Errorf("Expected version '0.4.0', got %v", result["version"])
		}
	})

	t.Run("FullCheck", func(t *testing.T) {
		result := hc.Check()

		if result.Version != "0.4.0" {
			t.Errorf("Expected version '0.4.0', got %s", result.Version)
		}
		if result.System == nil {
			t.Error("Expected system info to be present")
		}
		if result.System.NumCPU <= 0 {
			t.Error("Expected positive CPU count")
		}
	})
}

func TestAPIResponses(t *testing.T) {
	t.Run("JSON Response", func(t *testing.T) {
		w := httptest.NewRecorder()

		api.JSON(w, map[string]string{"test": "value"}, nil)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var resp api.Response
		if err := json.NewDecoder(w.Body).Decode(&resp); err != nil {
			t.Fatalf("Failed to decode response: %v", err)
		}

		if !resp.Success {
			t.Error("Expected success to be true")
		}
	})

	t.Run("Error Response", func(t *testing.T) {
		w := httptest.NewRecorder()

		api.Error(w, http.StatusBadRequest, "TEST_ERROR", "Test message", "details")

		if w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 400, got %d", w.Code)
		}

		var resp api.Response
		if err := json.NewDecoder(w.Body).Decode(&resp); err != nil {
			t.Fatalf("Failed to decode response: %v", err)
		}

		if resp.Success {
			t.Error("Expected success to be false")
		}
		if resp.Error == nil {
			t.Error("Expected error info to be present")
		}
		if resp.Error.Code != "TEST_ERROR" {
			t.Errorf("Expected error code 'TEST_ERROR', got %s", resp.Error.Code)
		}
	})

	t.Run("ToolUnavailable Response", func(t *testing.T) {
		w := httptest.NewRecorder()

		api.ToolUnavailable(w, "TestTool", "Install via: test install")

		if w.Code != http.StatusServiceUnavailable {
			t.Errorf("Expected status 503, got %d", w.Code)
		}

		var resp api.Response
		json.NewDecoder(w.Body).Decode(&resp)

		if resp.Error.Help == "" {
			t.Error("Expected help text to be present")
		}
	})
}

func TestFeatureRegistry(t *testing.T) {
	registry := api.NewFeatureRegistry()

	t.Run("Register and Get", func(t *testing.T) {
		registry.Register("test_feature", &api.FeatureStatus{
			Available: true,
		})

		status := registry.Get("test_feature")
		if !status.Available {
			t.Error("Expected feature to be available")
		}
	})

	t.Run("Unknown Feature", func(t *testing.T) {
		status := registry.Get("unknown")
		if status.Available {
			t.Error("Expected unknown feature to be unavailable")
		}
	})

	t.Run("IsAvailable", func(t *testing.T) {
		registry.Register("available_feature", &api.FeatureStatus{Available: true})
		registry.Register("unavailable_feature", &api.FeatureStatus{Available: false})

		if !registry.IsAvailable("available_feature") {
			t.Error("Expected available_feature to be available")
		}
		if registry.IsAvailable("unavailable_feature") {
			t.Error("Expected unavailable_feature to be unavailable")
		}
	})
}

func TestFeatureHelpers(t *testing.T) {
	t.Run("PandocFeature Available", func(t *testing.T) {
		status := api.PandocFeature(true, "3.0")
		if !status.Available {
			t.Error("Expected pandoc to be available")
		}
	})

	t.Run("PandocFeature Unavailable", func(t *testing.T) {
		status := api.PandocFeature(false, "")
		if status.Available {
			t.Error("Expected pandoc to be unavailable")
		}
		if status.InstallHelp == "" {
			t.Error("Expected install help to be present")
		}
	})

	t.Run("FFmpegFeature", func(t *testing.T) {
		status := api.FFmpegFeature(false)
		if status.Available {
			t.Error("Expected ffmpeg to be unavailable")
		}
		if !strings.Contains(status.InstallHelp, "winget") {
			t.Error("Expected winget install instructions")
		}
	})
}
