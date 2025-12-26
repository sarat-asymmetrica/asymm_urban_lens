package ocr_test

import (
	"context"
	"fmt"
	"image"
	"image/color"
	"testing"

	"github.com/asymmetrica/urbanlens/pkg/ocr"
)

// Example: Basic OCR usage
func ExampleDocumentOCR_basic() {
	// Create OCR processor
	ocrProcessor, err := ocr.NewDocumentOCR(nil) // Uses default Florence-2 config
	if err != nil {
		fmt.Printf("Failed to create OCR: %v\n", err)
		return
	}

	// Check health
	ctx := context.Background()
	if err := ocrProcessor.HealthCheck(ctx); err != nil {
		fmt.Printf("OCR service not available: %v\n", err)
		return
	}

	// Create a sample image (in real use, load from file)
	img := createSampleImage()

	// Extract text
	result, err := ocrProcessor.ExtractTextFromImage(ctx, img)
	if err != nil {
		fmt.Printf("OCR failed: %v\n", err)
		return
	}

	fmt.Printf("Extracted text: %s\n", result.Text)
	fmt.Printf("Confidence: %.2f\n", result.Confidence)
	fmt.Printf("Cost: $%.6f\n", result.Cost)
}

// Example: Batch OCR for multiple documents
func ExampleDocumentOCR_batch() {
	ocrProcessor, err := ocr.NewDocumentOCR(nil)
	if err != nil {
		fmt.Printf("Failed to create OCR: %v\n", err)
		return
	}

	// Create multiple images (e.g., survey pages)
	images := []image.Image{
		createSampleImage(),
		createSampleImage(),
		createSampleImage(),
	}

	// Batch extract
	ctx := context.Background()
	results, err := ocrProcessor.BatchExtract(ctx, images)
	if err != nil {
		fmt.Printf("Batch OCR failed: %v\n", err)
		return
	}

	fmt.Printf("Processed %d pages\n", len(results))
	for i, result := range results {
		fmt.Printf("Page %d: %d characters, confidence %.2f\n",
			i+1, len(result.Text), result.Confidence)
	}

	// Get statistics
	fmt.Println(ocrProcessor.GetStats())
}

// Example: Custom configuration
func ExampleDocumentOCR_custom() {
	// Use custom Florence-2 endpoint (e.g., self-hosted)
	config := &ocr.DocumentOCRConfig{
		Florence2URL: "http://localhost:8000", // Local deployment
	}

	ocrProcessor, err := ocr.NewDocumentOCR(config)
	if err != nil {
		fmt.Printf("Failed to create OCR: %v\n", err)
		return
	}

	fmt.Printf("OCR configured with custom endpoint\n")

	// Use as normal
	ctx := context.Background()
	if err := ocrProcessor.HealthCheck(ctx); err != nil {
		fmt.Printf("Custom endpoint not reachable: %v\n", err)
	}
}

// Helper function to create a sample image for testing
func createSampleImage() image.Image {
	// Create a simple 100x100 white image
	img := image.NewRGBA(image.Rect(0, 0, 100, 100))
	white := color.RGBA{255, 255, 255, 255}

	for y := 0; y < 100; y++ {
		for x := 0; x < 100; x++ {
			img.Set(x, y, white)
		}
	}

	return img
}

// Test: Verify OCR initialization
func TestDocumentOCR_Initialize(t *testing.T) {
	ocrProcessor, err := ocr.NewDocumentOCR(nil)
	if err != nil {
		t.Fatalf("Failed to create OCR: %v", err)
	}

	if ocrProcessor == nil {
		t.Fatal("OCR processor is nil")
	}
}

// Test: Verify custom config
func TestDocumentOCR_CustomConfig(t *testing.T) {
	config := &ocr.DocumentOCRConfig{
		Florence2URL: "https://custom-endpoint.example.com",
	}

	ocrProcessor, err := ocr.NewDocumentOCR(config)
	if err != nil {
		t.Fatalf("Failed to create OCR with custom config: %v", err)
	}

	if ocrProcessor == nil {
		t.Fatal("OCR processor is nil")
	}
}
