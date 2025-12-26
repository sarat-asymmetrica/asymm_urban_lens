package transcription

import (
	"testing"
)

func TestWhisperClient_Status(t *testing.T) {
	client := NewWhisperClient("")

	status := client.GetStatus()

	if status["configured"].(bool) {
		t.Error("Expected unconfigured client without API key")
	}

	formats := status["supported_formats"].([]string)
	if len(formats) == 0 {
		t.Error("Expected supported formats")
	}
}

func TestWhisperClient_SupportedLanguages(t *testing.T) {
	client := NewWhisperClient("")

	languages := client.SupportedLanguages()

	// Check for Indian languages
	if _, ok := languages["hi"]; !ok {
		t.Error("Expected Hindi support")
	}
	if _, ok := languages["ta"]; !ok {
		t.Error("Expected Tamil support")
	}
	if _, ok := languages["kn"]; !ok {
		t.Error("Expected Kannada support")
	}
}

func TestDetectLanguageFromText(t *testing.T) {
	tests := []struct {
		text     string
		expected string
	}{
		{"Hello world", "en"},
		{"नमस्ते दुनिया", "hi"},
		{"வணக்கம் உலகம்", "ta"},
		{"నమస్కారం ప్రపంచం", "te"},
		{"ನಮಸ್ಕಾರ ಪ್ರಪಂಚ", "kn"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			result := detectLanguageFromText(tt.text)
			if result != tt.expected {
				t.Errorf("detectLanguageFromText(%q) = %s, want %s", tt.text, result, tt.expected)
			}
		})
	}
}

func TestGenerateSRT(t *testing.T) {
	result := &TranscriptionResult{
		Segments: []Segment{
			{ID: 0, Start: 0.0, End: 2.5, Text: "Hello world"},
			{ID: 1, Start: 2.5, End: 5.0, Text: "This is a test"},
		},
	}

	srt := GenerateSRT(result)

	if srt == "" {
		t.Error("Expected SRT output")
	}

	if !contains(srt, "00:00:00,000 --> 00:00:02,500") {
		t.Error("Expected proper SRT timestamp format")
	}

	if !contains(srt, "Hello world") {
		t.Error("Expected text content in SRT")
	}
}

func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > 0 && containsHelper(s, substr))
}

func containsHelper(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
