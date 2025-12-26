// Package aimlapi - Tests
package aimlapi

import (
	"context"
	"os"
	"testing"
)

func TestNewClient(t *testing.T) {
	client := NewClient("test-key")
	if client == nil {
		t.Fatal("NewClient returned nil")
	}

	if !client.IsConfigured() {
		t.Error("Client should be configured with API key")
	}
}

func TestDefaultConfig(t *testing.T) {
	config := DefaultConfig()
	if config == nil {
		t.Fatal("DefaultConfig returned nil")
	}

	if config.BaseURL != "https://api.aimlapi.com/v1" {
		t.Errorf("Expected base URL https://api.aimlapi.com/v1, got %s", config.BaseURL)
	}

	if config.Regime != 2 {
		t.Errorf("Expected regime 2, got %d", config.Regime)
	}
}

func TestSetRegime(t *testing.T) {
	client := NewClient("test-key")

	// Test valid regimes
	for regime := 1; regime <= 3; regime++ {
		client.SetRegime(regime)
		if client.GetRegime() != regime {
			t.Errorf("Expected regime %d, got %d", regime, client.GetRegime())
		}
	}

	// Test invalid regime (should not change)
	client.SetRegime(2)
	client.SetRegime(5)
	if client.GetRegime() != 2 {
		t.Error("Invalid regime should not change current regime")
	}
}

func TestListModels(t *testing.T) {
	client := NewClient("test-key")
	models := client.ListModels()

	if len(models) == 0 {
		t.Error("ListModels returned empty list")
	}

	// Check for key models
	foundGPT4o := false
	foundClaude := false
	foundGemini := false

	for _, model := range models {
		if model.ModelID == "gpt-4o" || model.Name == "GPT-4o" {
			foundGPT4o = true
		}
		if model.ModelID == "claude-sonnet" || model.Name == "Claude 3.5 Sonnet" {
			foundClaude = true
		}
		if model.ModelID == "gemini-flash" || model.Name == "Gemini 1.5 Flash" {
			foundGemini = true
		}
	}

	if !foundGPT4o {
		t.Error("gpt-4o not found in model list")
	}
	if !foundClaude {
		t.Error("claude-sonnet not found in model list")
	}
	if !foundGemini {
		t.Error("gemini-flash not found in model list")
	}
}

func TestGetModel(t *testing.T) {
	client := NewClient("test-key")

	model, err := client.GetModel("gpt-4o")
	if err != nil {
		t.Fatalf("GetModel failed: %v", err)
	}

	if model.Name != "GPT-4o" {
		t.Errorf("Expected name GPT-4o, got %s", model.Name)
	}

	if model.Provider != "openai" {
		t.Errorf("Expected provider openai, got %s", model.Provider)
	}
}

func TestSelectModel(t *testing.T) {
	client := NewClient("test-key")

	// Test code task
	constraints := SelectionConstraints{
		TaskType:   TASK_CODE,
		MinQuality: 8.0,
	}

	model, err := client.SelectModel(constraints)
	if err != nil {
		t.Fatalf("SelectModel failed: %v", err)
	}

	if model.Capabilities&CODE == 0 {
		t.Error("Selected model should have CODE capability")
	}

	// Test vision task
	constraints = SelectionConstraints{
		TaskType:      TASK_VISION,
		RequireVision: true,
	}

	model, err = client.SelectModel(constraints)
	if err != nil {
		t.Fatalf("SelectModel failed: %v", err)
	}

	if model.Capabilities&VISION == 0 {
		t.Error("Selected model should have VISION capability")
	}
}

func TestConversation(t *testing.T) {
	conv := NewConversation()

	if conv.GetMessageCount() != 0 {
		t.Error("New conversation should have 0 messages")
	}

	conv.AddSystem("You are a helpful assistant")
	conv.AddUser("Hello")
	conv.AddAssistant("Hi there!")

	if conv.GetMessageCount() != 3 {
		t.Errorf("Expected 3 messages, got %d", conv.GetMessageCount())
	}

	lastMsg := conv.GetLastMessage()
	if lastMsg == nil {
		t.Fatal("GetLastMessage returned nil")
	}

	if lastMsg.Role != "assistant" {
		t.Errorf("Expected last message role 'assistant', got %s", lastMsg.Role)
	}

	conv.Reset()
	if conv.GetMessageCount() != 0 {
		t.Error("Reset should clear all messages")
	}
}

func TestEstimateTokens(t *testing.T) {
	text := "This is a test message"
	tokens := EstimateTokens(text)

	if tokens <= 0 {
		t.Error("EstimateTokens should return positive value")
	}

	// Rough check (1 token ≈ 4 chars)
	expectedRange := len(text) / 6 // Allow some variance
	if tokens < expectedRange || tokens > len(text) {
		t.Logf("Warning: token estimate may be off. Got %d for %d chars", tokens, len(text))
	}
}

func TestWilliamsBatchSize(t *testing.T) {
	tests := []struct {
		n        int
		expected int // rough expectation
	}{
		{1, 1},
		{10, 3}, // √10 × log₂(10) ≈ 3.16 × 3.32 ≈ 10.5, clamped
		{100, 20}, // √100 × log₂(100) ≈ 10 × 6.64 ≈ 66.4, clamped to 20
	}

	for _, test := range tests {
		size := calculateWilliamsBatchSize(test.n)
		if size < 1 || size > 20 {
			t.Errorf("Batch size for n=%d out of bounds: %d", test.n, size)
		}
	}
}

func TestRateLimiter(t *testing.T) {
	rl := NewRateLimiter(60) // 60 requests/minute = 1/sec

	ctx := context.Background()

	// Should allow first request immediately
	err := rl.Wait(ctx)
	if err != nil {
		t.Fatalf("First request should succeed: %v", err)
	}
}

func TestValidateRequest(t *testing.T) {
	// Valid request
	req := ChatRequest{
		Model: "gpt-4o",
		Messages: []Message{
			{Role: "user", Content: "Hello"},
		},
		Temperature: 0.7,
	}

	if err := ValidateRequest(req); err != nil {
		t.Errorf("Valid request failed validation: %v", err)
	}

	// Missing model
	req.Model = ""
	if err := ValidateRequest(req); err == nil {
		t.Error("Should reject request with missing model")
	}
	req.Model = "gpt-4o"

	// Invalid temperature
	req.Temperature = 3.0
	if err := ValidateRequest(req); err == nil {
		t.Error("Should reject request with invalid temperature")
	}
}

// Integration tests (require AIMLAPI_KEY)
func TestIntegrationSimpleChat(t *testing.T) {
	apiKey := os.Getenv("AIMLAPI_KEY")
	if apiKey == "" {
		t.Skip("AIMLAPI_KEY not set, skipping integration test")
	}

	client := NewClient(apiKey)
	ctx := context.Background()

	resp, err := client.SimpleChat(ctx, "Say 'hello' in one word")
	if err != nil {
		t.Fatalf("SimpleChat failed: %v", err)
	}

	if resp == "" {
		t.Error("Response should not be empty")
	}

	t.Logf("Response: %s", resp)
}

func TestIntegrationHealthCheck(t *testing.T) {
	apiKey := os.Getenv("AIMLAPI_KEY")
	if apiKey == "" {
		t.Skip("AIMLAPI_KEY not set, skipping integration test")
	}

	client := NewClient(apiKey)
	ctx := context.Background()

	if err := client.HealthCheck(ctx); err != nil {
		t.Fatalf("HealthCheck failed: %v", err)
	}
}
