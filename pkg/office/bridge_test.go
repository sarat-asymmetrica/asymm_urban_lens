package office

import (
	"testing"
)

func TestBridge_New(t *testing.T) {
	bridge := NewBridge()
	if bridge == nil {
		t.Fatal("NewBridge returned nil")
	}
}

func TestBridge_IsAvailable(t *testing.T) {
	bridge := NewBridge()

	// Runtime likely not running in test environment
	// Just verify the method works
	available := bridge.IsAvailable()
	t.Logf("Asymmetrica.Runtime available: %v", available)
}

func TestBridge_GetStatus(t *testing.T) {
	bridge := NewBridge()

	status := bridge.GetStatus()

	if status["available"] == nil {
		t.Error("Expected 'available' in status")
	}
	if status["endpoint"] == nil {
		t.Error("Expected 'endpoint' in status")
	}
	if status["install_help"] == nil {
		t.Error("Expected 'install_help' in status")
	}
}

func TestBridge_CustomURL(t *testing.T) {
	bridge := NewBridgeWithURL("http://localhost:9999")

	if bridge.baseURL != "http://localhost:9999" {
		t.Errorf("Expected custom URL, got %s", bridge.baseURL)
	}
}
