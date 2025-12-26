// Package transcription provides audio transcription via Whisper API
// Supports both AIMLAPI and local ffmpeg preprocessing
package transcription

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"mime/multipart"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/media"
)

// WhisperClient handles audio transcription via Whisper API
type WhisperClient struct {
	apiKey     string
	baseURL    string
	httpClient *http.Client
	ffmpeg     *media.FFmpegProcessor
}

// TranscriptionRequest represents a transcription request
type TranscriptionRequest struct {
	FilePath    string  `json:"file_path"`
	Language    string  `json:"language,omitempty"`    // ISO-639-1 code (e.g., "en", "hi", "ta")
	Prompt      string  `json:"prompt,omitempty"`      // Context hint
	Temperature float64 `json:"temperature,omitempty"` // 0-1, lower = more deterministic
	Format      string  `json:"format,omitempty"`      // "json", "text", "srt", "vtt"
}

// TranscriptionResult contains the transcription output
type TranscriptionResult struct {
	Text        string        `json:"text"`
	Language    string        `json:"language,omitempty"`
	Duration    float64       `json:"duration,omitempty"`
	Segments    []Segment     `json:"segments,omitempty"`
	Words       []Word        `json:"words,omitempty"`
	ProcessTime time.Duration `json:"process_time"`
}

// Segment represents a transcription segment with timing
type Segment struct {
	ID    int     `json:"id"`
	Start float64 `json:"start"`
	End   float64 `json:"end"`
	Text  string  `json:"text"`
}

// Word represents a word with timing (word-level timestamps)
type Word struct {
	Word  string  `json:"word"`
	Start float64 `json:"start"`
	End   float64 `json:"end"`
}

// NewWhisperClient creates a new Whisper transcription client
func NewWhisperClient(apiKey string) *WhisperClient {
	if apiKey == "" {
		apiKey = os.Getenv("AIMLAPI_KEY")
	}

	return &WhisperClient{
		apiKey:  apiKey,
		baseURL: "https://api.aimlapi.com/v1",
		httpClient: &http.Client{
			Timeout: 300 * time.Second, // 5 min for long audio
		},
		ffmpeg: media.NewFFmpegProcessor(),
	}
}

// IsConfigured returns true if API key is set
func (w *WhisperClient) IsConfigured() bool {
	return w.apiKey != ""
}

// Transcribe transcribes an audio file
func (w *WhisperClient) Transcribe(ctx context.Context, req TranscriptionRequest) (*TranscriptionResult, error) {
	if !w.IsConfigured() {
		return nil, fmt.Errorf("AIMLAPI_KEY not configured")
	}

	start := time.Now()

	// Preprocess audio if ffmpeg available (optimize for Whisper)
	audioPath := req.FilePath
	var tempFile string

	if w.ffmpeg.Available {
		// Convert to 16kHz mono WAV for optimal Whisper performance
		tempFile = filepath.Join(os.TempDir(), "whisper_"+filepath.Base(req.FilePath)+".wav")
		result, err := w.ffmpeg.ExtractAudioForTranscription(req.FilePath, tempFile)
		if err == nil && result.Success {
			audioPath = tempFile
			defer os.Remove(tempFile)
		}
	}

	// Open audio file
	file, err := os.Open(audioPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open audio file: %w", err)
	}
	defer file.Close()

	// Create multipart form
	var buf bytes.Buffer
	writer := multipart.NewWriter(&buf)

	// Add file
	part, err := writer.CreateFormFile("file", filepath.Base(audioPath))
	if err != nil {
		return nil, fmt.Errorf("failed to create form file: %w", err)
	}
	if _, err := io.Copy(part, file); err != nil {
		return nil, fmt.Errorf("failed to copy file: %w", err)
	}

	// Add model
	writer.WriteField("model", "whisper-1")

	// Add optional parameters
	if req.Language != "" {
		writer.WriteField("language", req.Language)
	}
	if req.Prompt != "" {
		writer.WriteField("prompt", req.Prompt)
	}
	if req.Temperature > 0 {
		writer.WriteField("temperature", fmt.Sprintf("%.2f", req.Temperature))
	}

	// Request verbose JSON for segments
	format := req.Format
	if format == "" {
		format = "verbose_json"
	}
	writer.WriteField("response_format", format)

	writer.Close()

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", w.baseURL+"/audio/transcriptions", &buf)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", "Bearer "+w.apiKey)
	httpReq.Header.Set("Content-Type", writer.FormDataContentType())

	// Execute request
	resp, err := w.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("transcription request failed: %w", err)
	}
	defer resp.Body.Close()

	// Read response
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("transcription failed (status %d): %s", resp.StatusCode, string(body))
	}

	// Parse response
	var result TranscriptionResult
	if format == "text" {
		result.Text = string(body)
	} else {
		if err := json.Unmarshal(body, &result); err != nil {
			// Try simple text response
			result.Text = string(body)
		}
	}

	result.ProcessTime = time.Since(start)

	return &result, nil
}

// TranscribeWithTimestamps transcribes with word-level timestamps
func (w *WhisperClient) TranscribeWithTimestamps(ctx context.Context, filePath string, language string) (*TranscriptionResult, error) {
	return w.Transcribe(ctx, TranscriptionRequest{
		FilePath: filePath,
		Language: language,
		Format:   "verbose_json",
	})
}

// TranscribeSimple returns just the text transcription
func (w *WhisperClient) TranscribeSimple(ctx context.Context, filePath string) (string, error) {
	result, err := w.Transcribe(ctx, TranscriptionRequest{
		FilePath: filePath,
		Format:   "text",
	})
	if err != nil {
		return "", err
	}
	return result.Text, nil
}

// SupportedFormats returns supported audio formats
func (w *WhisperClient) SupportedFormats() []string {
	return []string{
		"mp3", "mp4", "mpeg", "mpga", "m4a",
		"wav", "webm", "flac", "ogg",
	}
}

// SupportedLanguages returns commonly supported languages
func (w *WhisperClient) SupportedLanguages() map[string]string {
	return map[string]string{
		"en": "English",
		"hi": "Hindi",
		"ta": "Tamil",
		"te": "Telugu",
		"kn": "Kannada",
		"ml": "Malayalam",
		"mr": "Marathi",
		"bn": "Bengali",
		"gu": "Gujarati",
		"pa": "Punjabi",
		"ur": "Urdu",
		"es": "Spanish",
		"fr": "French",
		"de": "German",
		"zh": "Chinese",
		"ja": "Japanese",
		"ko": "Korean",
		"ar": "Arabic",
		"pt": "Portuguese",
		"ru": "Russian",
	}
}

// GetStatus returns the client status
func (w *WhisperClient) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"configured":          w.IsConfigured(),
		"ffmpeg_available":    w.ffmpeg.Available,
		"supported_formats":   w.SupportedFormats(),
		"supported_languages": w.SupportedLanguages(),
	}
}

// DetectLanguage detects the language of an audio file
func (w *WhisperClient) DetectLanguage(ctx context.Context, filePath string) (string, error) {
	// Transcribe a small portion to detect language
	result, err := w.Transcribe(ctx, TranscriptionRequest{
		FilePath: filePath,
		Format:   "verbose_json",
	})
	if err != nil {
		return "", err
	}

	if result.Language != "" {
		return result.Language, nil
	}

	// Fallback: detect from text
	return detectLanguageFromText(result.Text), nil
}

// detectLanguageFromText is a simple heuristic language detector
func detectLanguageFromText(text string) string {
	// Simple heuristic based on character ranges
	for _, r := range text {
		if r >= 0x0900 && r <= 0x097F {
			return "hi" // Devanagari (Hindi)
		}
		if r >= 0x0B80 && r <= 0x0BFF {
			return "ta" // Tamil
		}
		if r >= 0x0C00 && r <= 0x0C7F {
			return "te" // Telugu
		}
		if r >= 0x0C80 && r <= 0x0CFF {
			return "kn" // Kannada
		}
		if r >= 0x0D00 && r <= 0x0D7F {
			return "ml" // Malayalam
		}
		if r >= 0x4E00 && r <= 0x9FFF {
			return "zh" // Chinese
		}
		if r >= 0x3040 && r <= 0x309F {
			return "ja" // Japanese Hiragana
		}
	}

	// Default to English
	return "en"
}

// GenerateSRT generates SRT subtitle format from transcription
func GenerateSRT(result *TranscriptionResult) string {
	if len(result.Segments) == 0 {
		return ""
	}

	var sb strings.Builder
	for i, seg := range result.Segments {
		sb.WriteString(fmt.Sprintf("%d\n", i+1))
		sb.WriteString(fmt.Sprintf("%s --> %s\n", formatSRTTime(seg.Start), formatSRTTime(seg.End)))
		sb.WriteString(seg.Text + "\n\n")
	}
	return sb.String()
}

// formatSRTTime formats seconds to SRT timestamp (HH:MM:SS,mmm)
func formatSRTTime(seconds float64) string {
	hours := int(seconds) / 3600
	minutes := (int(seconds) % 3600) / 60
	secs := int(seconds) % 60
	millis := int((seconds - float64(int(seconds))) * 1000)
	return fmt.Sprintf("%02d:%02d:%02d,%03d", hours, minutes, secs, millis)
}
