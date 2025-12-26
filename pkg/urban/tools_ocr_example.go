package urban

import (
	"context"
	"fmt"
	"image"

	"github.com/asymmetrica/urbanlens/pkg/ocr"
)

// Example: How to use OCR with DocumentProcessor
//
// This shows how UrbanLens researchers can use Florence-2 OCR
// for policy analysis, census extraction, and survey processing.

// ProcessDocumentWithOCR processes a document image using OCR
func (d *DocumentProcessor) ProcessWithOCR(ctx context.Context, img image.Image) (*DocumentResult, error) {
	if !d.OCREnabled {
		return nil, fmt.Errorf("OCR not enabled for this processor")
	}

	// Create OCR processor
	ocrProcessor, err := ocr.NewDocumentOCR(nil)
	if err != nil {
		return nil, fmt.Errorf("failed to initialize OCR: %w", err)
	}

	// Extract text using Florence-2
	ocrResult, err := ocrProcessor.ExtractTextFromImage(ctx, img)
	if err != nil {
		return nil, fmt.Errorf("OCR extraction failed: %w", err)
	}

	// Convert to DocumentResult
	result := &DocumentResult{
		Filename:      "ocr_document.png",
		FileType:      "image",
		PageCount:     ocrResult.PageCount,
		ExtractedText: ocrResult.Text,
		Tables:        []TableData{}, // Future: extract tables from OCR
		Confidence:    ocrResult.Confidence,
		Language:      ocrResult.Language,
		Metadata: map[string]interface{}{
			"ocr_duration": ocrResult.Duration,
			"ocr_cost":     ocrResult.Cost,
		},
	}

	return result, nil
}

// BatchProcessWithOCR processes multiple document images using batch OCR
func (d *DocumentProcessor) BatchProcessWithOCR(ctx context.Context, images []image.Image) ([]*DocumentResult, error) {
	if !d.OCREnabled {
		return nil, fmt.Errorf("OCR not enabled for this processor")
	}

	// Create OCR processor
	ocrProcessor, err := ocr.NewDocumentOCR(nil)
	if err != nil {
		return nil, fmt.Errorf("failed to initialize OCR: %w", err)
	}

	// Batch extract text
	ocrResults, err := ocrProcessor.BatchExtract(ctx, images)
	if err != nil {
		return nil, fmt.Errorf("batch OCR failed: %w", err)
	}

	// Convert to DocumentResults
	results := make([]*DocumentResult, len(ocrResults))
	for i, ocrResult := range ocrResults {
		results[i] = &DocumentResult{
			Filename:      fmt.Sprintf("ocr_document_%d.png", i+1),
			FileType:      "image",
			PageCount:     ocrResult.PageCount,
			ExtractedText: ocrResult.Text,
			Tables:        []TableData{},
			Confidence:    ocrResult.Confidence,
			Language:      ocrResult.Language,
			Metadata: map[string]interface{}{
				"ocr_duration": ocrResult.Duration,
				"ocr_cost":     ocrResult.Cost,
			},
		}
	}

	return results, nil
}

// ExampleUsage shows how IIHS researchers use OCR
func ExampleDocumentProcessor_OCR() {
	// Create tool registry
	registry := NewToolRegistry()

	// Scenario: Process a policy document image
	ctx := context.Background()

	// Load policy document image (in real use)
	// policyImage, _ := loadImageFromFile("urban_policy_2024.png")

	// For demonstration, create a sample image
	policyImage := createSamplePolicyImage()

	// Process with OCR
	result, err := registry.Document.ProcessWithOCR(ctx, policyImage)
	if err != nil {
		fmt.Printf("Failed to process document: %v\n", err)
		return
	}

	fmt.Printf("Policy Document OCR Results:\n")
	fmt.Printf("  Extracted: %d characters\n", len(result.ExtractedText))
	fmt.Printf("  Confidence: %.2f\n", result.Confidence)
	fmt.Printf("  Language: %s\n", result.Language)
	fmt.Printf("  Duration: %v\n", result.Metadata["ocr_duration"])
	fmt.Printf("  Cost: $%.6f\n", result.Metadata["ocr_cost"])

	// Use extracted text for analysis
	// - Policy language analysis
	// - Topic extraction
	// - Comparison with previous policies
}

// ExampleBatchSurveyProcessing shows batch survey processing
func ExampleDocumentProcessor_BatchSurvey() {
	registry := NewToolRegistry()
	ctx := context.Background()

	// Load survey pages (in real use)
	surveyPages := []image.Image{
		createSamplePolicyImage(), // Page 1
		createSamplePolicyImage(), // Page 2
		createSamplePolicyImage(), // Page 3
	}

	// Batch process
	results, err := registry.Document.BatchProcessWithOCR(ctx, surveyPages)
	if err != nil {
		fmt.Printf("Failed to batch process: %v\n", err)
		return
	}

	fmt.Printf("Survey Processing Results:\n")
	totalCost := 0.0
	totalChars := 0

	for i, result := range results {
		fmt.Printf("  Page %d: %d characters, confidence %.2f\n",
			i+1, len(result.ExtractedText), result.Confidence)

		totalCost += result.Metadata["ocr_cost"].(float64)
		totalChars += len(result.ExtractedText)
	}

	fmt.Printf("\nSummary:\n")
	fmt.Printf("  Total pages: %d\n", len(results))
	fmt.Printf("  Total characters: %d\n", totalChars)
	fmt.Printf("  Total cost: $%.6f\n", totalCost)

	// Process survey responses
	// - Extract demographic data
	// - Analyze response patterns
	// - Validate against codebook
}

// Helper: Create sample policy image for demonstration
func createSamplePolicyImage() image.Image {
	// In real use, this would load from file
	// For demo, return a simple image
	img := image.NewRGBA(image.Rect(0, 0, 100, 100))

	// Fill with white
	for y := 0; y < 100; y++ {
		for x := 0; x < 100; x++ {
			img.Set(x, y, image.White)
		}
	}

	return img
}
