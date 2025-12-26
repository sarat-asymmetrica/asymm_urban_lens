package chat

import (
	"testing"
)

func TestService_Status(t *testing.T) {
	service := NewService("")

	status := service.GetStatus()

	if status["configured"].(bool) {
		t.Error("Expected unconfigured service without API key")
	}

	models := status["available_models"].([]string)
	if len(models) == 0 {
		t.Error("Expected available models list")
	}
}

func TestService_SystemPrompt(t *testing.T) {
	service := NewService("")

	// Check default prompt
	prompt := service.GetSystemPrompt()
	if prompt == "" {
		t.Error("Expected default system prompt")
	}

	// Check it contains Urban Lens identity
	if !containsString(prompt, "Urban Lens") {
		t.Error("Expected Urban Lens in system prompt")
	}

	// Test custom prompt
	service.SetSystemPrompt("Custom prompt")
	if service.GetSystemPrompt() != "Custom prompt" {
		t.Error("Expected custom prompt to be set")
	}
}

func TestDefaultSystemPrompt(t *testing.T) {
	// Verify key elements are present
	if !containsString(DefaultSystemPrompt, "IIHS") {
		t.Error("Expected IIHS mention in prompt")
	}
	if !containsString(DefaultSystemPrompt, "urban") {
		t.Error("Expected urban research context")
	}
	if !containsString(DefaultSystemPrompt, "research") {
		t.Error("Expected research context")
	}
}

func containsString(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
