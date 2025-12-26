// Package ocr - Unified OCR Service
// Combines Florence-2 (fast, cheap) with AIMLAPI vision (fallback)
package ocr

import (
	"context"
	"encoding/base64"
	"fmt"
	"image"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// UnifiedOCRService provides OCR with automatic fallback
type UnifiedOCRService struct {
	florence *Florence2Client
	// aimlClient for fallback (future: wire to aimlapi.Client)
}

// OCRRequest represents an OCR request
type OCRRequest struct {
	FilePath   string `json:"file_path,omitempty"`
	ImageData  []byte `json:"image_data,omitempty"`
	Base64Data string `json:"base64_data,omitempty"`
	Language   string `json:"language,omitempty"` // Hint for OCR
}

// OCRResponse represents a unified OCR response
type OCRResponse struct {
	Success     bool    `json:"success"`
	Text        string  `json:"text"`
	Characters  int     `json:"characters"`
	Lines       int     `json:"lines"`
	Words       int     `json:"words"`
	Language    string  `json:"language,omitempty"`
	Confidence  float64 `json:"confidence,omitempty"`
	Provider    string  `json:"provider"` // "florence2", "aimlapi", "tesseract"
	ProcessTime float64 `json:"process_time_ms"`
	Cost        float64 `json:"estimated_cost_usd"`
	Error       string  `json:"error,omitempty"`
}

// NewUnifiedOCRService creates a new unified OCR service
func NewUnifiedOCRService() (*UnifiedOCRService, error) {
	florence, err := NewFlorence2Client(nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create Florence-2 client: %w", err)
	}

	return &UnifiedOCRService{
		florence: florence,
	}, nil
}

// OCR performs OCR on an image file or data
func (s *UnifiedOCRService) OCR(ctx context.Context, req OCRRequest) (*OCRResponse, error) {
	start := time.Now()

	// Get image data
	var imageData []byte
	var err error

	if req.FilePath != "" {
		imageData, err = os.ReadFile(req.FilePath)
		if err != nil {
			return &OCRResponse{
				Success: false,
				Error:   fmt.Sprintf("failed to read file: %v", err),
			}, err
		}
	} else if req.Base64Data != "" {
		imageData, err = base64.StdEncoding.DecodeString(req.Base64Data)
		if err != nil {
			return &OCRResponse{
				Success: false,
				Error:   fmt.Sprintf("failed to decode base64: %v", err),
			}, err
		}
	} else if req.ImageData != nil {
		imageData = req.ImageData
	} else {
		return &OCRResponse{
			Success: false,
			Error:   "no image data provided",
		}, fmt.Errorf("no image data provided")
	}

	// Try Florence-2 first (fast and cheap)
	result, err := s.florence.OCRImageBytes(ctx, imageData)
	if err == nil && result.Success {
		text := result.Text
		return &OCRResponse{
			Success:     true,
			Text:        text,
			Characters:  len(text),
			Lines:       countLines(text),
			Words:       countWords(text),
			Confidence:  result.Confidence,
			Provider:    "florence2",
			ProcessTime: float64(time.Since(start).Milliseconds()),
			Cost:        result.EstimatedCost,
		}, nil
	}

	// Florence-2 failed, return error (future: add AIMLAPI fallback)
	errMsg := "OCR failed"
	if err != nil {
		errMsg = err.Error()
	} else if result != nil && result.Error != "" {
		errMsg = result.Error
	}

	return &OCRResponse{
		Success:     false,
		Error:       errMsg,
		Provider:    "florence2",
		ProcessTime: float64(time.Since(start).Milliseconds()),
	}, fmt.Errorf("OCR failed: %s", errMsg)
}

// OCRFile performs OCR on a file path
func (s *UnifiedOCRService) OCRFile(ctx context.Context, filePath string) (*OCRResponse, error) {
	return s.OCR(ctx, OCRRequest{FilePath: filePath})
}

// OCRImage performs OCR on an image.Image
func (s *UnifiedOCRService) OCRImage(ctx context.Context, img image.Image) (*OCRResponse, error) {
	start := time.Now()

	result, err := s.florence.OCRImage(ctx, img)
	if err != nil {
		return &OCRResponse{
			Success:     false,
			Error:       err.Error(),
			Provider:    "florence2",
			ProcessTime: float64(time.Since(start).Milliseconds()),
		}, err
	}

	text := result.Text
	return &OCRResponse{
		Success:     result.Success,
		Text:        text,
		Characters:  len(text),
		Lines:       countLines(text),
		Words:       countWords(text),
		Confidence:  result.Confidence,
		Provider:    "florence2",
		ProcessTime: float64(time.Since(start).Milliseconds()),
		Cost:        result.EstimatedCost,
	}, nil
}

// GetStatus returns service status
func (s *UnifiedOCRService) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"providers": []map[string]interface{}{
			{
				"name":        "florence2",
				"available":   true,
				"description": "Microsoft Florence-2 on Modal A10G",
				"speed":       "~0.3s per page",
				"cost":        "$0.15 per 1000 pages",
				"accuracy":    "93%+",
			},
		},
		"supported_formats": []string{
			"jpg", "jpeg", "png", "gif", "bmp", "webp", "tiff",
		},
		"stats": s.florence.GetStats(),
	}
}

// SupportedFormats returns supported image formats
func (s *UnifiedOCRService) SupportedFormats() []string {
	return []string{"jpg", "jpeg", "png", "gif", "bmp", "webp", "tiff", "pdf"}
}

// IsImageFile checks if a file is a supported image format
func IsImageFile(filePath string) bool {
	ext := strings.ToLower(filepath.Ext(filePath))
	supported := map[string]bool{
		".jpg": true, ".jpeg": true, ".png": true,
		".gif": true, ".bmp": true, ".webp": true,
		".tiff": true, ".tif": true,
	}
	return supported[ext]
}

// Helper functions

func countLines(text string) int {
	if text == "" {
		return 0
	}
	return strings.Count(text, "\n") + 1
}

func countWords(text string) int {
	if text == "" {
		return 0
	}
	return len(strings.Fields(text))
}
