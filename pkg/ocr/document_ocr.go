// Document OCR - Simplified OCR interface for UrbanLens research
//
// Designed for research use cases:
// - Policy document analysis
// - Census data extraction
// - Survey form processing
// - Urban planning documents
//
// Uses Florence-2 for fast, cost-effective OCR
package ocr

import (
	"bytes"
	"context"
	"fmt"
	"image"
	_ "image/jpeg"
	_ "image/png"
	"io"
)

// DocumentOCR provides OCR capabilities for research documents
type DocumentOCR struct {
	florence2 *Florence2Client
}

// DocumentOCRConfig configures document OCR
type DocumentOCRConfig struct {
	Florence2URL string
}

// NewDocumentOCR creates a new document OCR processor
func NewDocumentOCR(config *DocumentOCRConfig) (*DocumentOCR, error) {
	// Initialize Florence-2 client
	florence2Config := DefaultFlorence2Config()
	if config != nil && config.Florence2URL != "" {
		florence2Config.BaseURL = config.Florence2URL
	}

	florence2, err := NewFlorence2Client(florence2Config)
	if err != nil {
		return nil, fmt.Errorf("failed to initialize Florence-2: %w", err)
	}

	return &DocumentOCR{
		florence2: florence2,
	}, nil
}

// OCRResult represents OCR extraction result
type OCRResult struct {
	Text       string
	Confidence float64
	PageCount  int
	Language   string
	Duration   string
	Cost       float64
}

// ExtractTextFromImage extracts text from an image
func (d *DocumentOCR) ExtractTextFromImage(ctx context.Context, img image.Image) (*OCRResult, error) {
	// Use Florence-2 for OCR
	result, err := d.florence2.OCRImage(ctx, img)
	if err != nil {
		return nil, fmt.Errorf("Florence-2 OCR failed: %w", err)
	}

	if !result.Success {
		return nil, fmt.Errorf("OCR failed: %s", result.Error)
	}

	return &OCRResult{
		Text:       result.Text,
		Confidence: result.Confidence,
		PageCount:  1,
		Language:   "en", // Florence-2 auto-detects but primarily English
		Duration:   result.Duration.String(),
		Cost:       result.EstimatedCost,
	}, nil
}

// ExtractTextFromImageBytes extracts text from image bytes
func (d *DocumentOCR) ExtractTextFromImageBytes(ctx context.Context, imageData []byte) (*OCRResult, error) {
	// Decode image
	img, _, err := image.Decode(bytes.NewReader(imageData))
	if err != nil {
		return nil, fmt.Errorf("failed to decode image: %w", err)
	}

	return d.ExtractTextFromImage(ctx, img)
}

// ExtractTextFromPDF extracts text from a PDF file
// Note: This requires converting PDF pages to images first
func (d *DocumentOCR) ExtractTextFromPDF(ctx context.Context, pdfData []byte) (*OCRResult, error) {
	// For research purposes, we'll process as a single document
	// Production systems would:
	// 1. Convert PDF to images using MuPDF/Poppler
	// 2. OCR each page
	// 3. Combine results

	return nil, fmt.Errorf("PDF extraction requires PDF-to-image conversion (add MuPDF dependency if needed)")
}

// BatchExtract extracts text from multiple images efficiently
func (d *DocumentOCR) BatchExtract(ctx context.Context, images []image.Image) ([]*OCRResult, error) {
	// Use Florence-2 batch endpoint for efficiency
	batchResult, err := d.florence2.OCRBatch(ctx, images)
	if err != nil {
		return nil, fmt.Errorf("batch OCR failed: %w", err)
	}

	results := make([]*OCRResult, len(batchResult.Results))
	for i, r := range batchResult.Results {
		results[i] = &OCRResult{
			Text:       r.Text,
			Confidence: r.Confidence,
			PageCount:  1,
			Language:   "en",
			Duration:   r.Duration.String(),
			Cost:       r.EstimatedCost,
		}
	}

	return results, nil
}

// HealthCheck verifies OCR service is available
func (d *DocumentOCR) HealthCheck(ctx context.Context) error {
	return d.florence2.HealthCheck(ctx)
}

// GetStats returns OCR usage statistics
func (d *DocumentOCR) GetStats() string {
	return d.florence2.Summary()
}

// Helper: Load image from reader
func LoadImage(r io.Reader) (image.Image, error) {
	img, _, err := image.Decode(r)
	if err != nil {
		return nil, fmt.Errorf("failed to decode image: %w", err)
	}
	return img, nil
}
