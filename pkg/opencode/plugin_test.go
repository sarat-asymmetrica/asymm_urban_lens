package opencode

import (
	"testing"
)

func TestPlugin_New(t *testing.T) {
	plugin := NewPlugin()
	if plugin == nil {
		t.Fatal("NewPlugin returned nil")
	}
	if plugin.Name != "urban-lens" {
		t.Errorf("Expected name 'urban-lens', got %s", plugin.Name)
	}
}

func TestPlugin_GetManifest(t *testing.T) {
	plugin := NewPlugin()
	manifest := plugin.GetManifest()

	if manifest.Name != "urban-lens" {
		t.Errorf("Expected name 'urban-lens', got %s", manifest.Name)
	}
	if len(manifest.Commands) == 0 {
		t.Error("Expected at least one command")
	}
	if len(manifest.Capabilities) == 0 {
		t.Error("Expected at least one capability")
	}
}

func TestPlugin_GetToolDefinitions(t *testing.T) {
	plugin := NewPlugin()
	tools := plugin.GetToolDefinitions()

	if len(tools) == 0 {
		t.Error("Expected at least one tool definition")
	}

	// Check that each tool has required fields
	for _, tool := range tools {
		if tool.Name == "" {
			t.Error("Tool missing name")
		}
		if tool.Description == "" {
			t.Error("Tool missing description")
		}
		if tool.Endpoint == "" {
			t.Error("Tool missing endpoint")
		}
	}
}

func TestPlugin_GetStatus(t *testing.T) {
	plugin := NewPlugin()
	status := plugin.GetStatus()

	if status["name"] == nil {
		t.Error("Expected 'name' in status")
	}
	if status["version"] == nil {
		t.Error("Expected 'version' in status")
	}
	if status["commands"] == nil {
		t.Error("Expected 'commands' in status")
	}
}
